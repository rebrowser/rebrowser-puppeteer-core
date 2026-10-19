/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

import type {Protocol} from 'devtools-protocol';

import {CDPSessionEvent, type CDPSession} from '../api/CDPSession.js';
import type {ElementHandle} from '../api/ElementHandle.js';
import type {JSHandle} from '../api/JSHandle.js';
import {ARIAQueryHandler} from '../common/AriaQueryHandler.js';
import {DEBUG_PREFIXES, type Logger} from '../common/Debug.js';
import {EventEmitter} from '../common/EventEmitter.js';
import {LazyArg} from '../common/LazyArg.js';
import {scriptInjector} from '../common/ScriptInjector.js';
import type {BindingPayload, EvaluateFunc, HandleFor} from '../common/types.js';
import {
  PuppeteerURL,
  SOURCE_URL_REGEX,
  getSourcePuppeteerURLIfAvailable,
  getSourceUrlComment,
  isString,
} from '../common/util.js';
import type {PuppeteerInjectedUtil} from '../injected/injected.js';
import {AsyncIterableUtil} from '../util/AsyncIterableUtil.js';
import {DisposableStack, disposeSymbol} from '../util/disposable.js';
import {stringifyFunction} from '../util/Function.js';
import {Mutex} from '../util/Mutex.js';

import {Binding} from './Binding.js';
import {CdpElementHandle} from './ElementHandle.js';
import type {IsolatedWorld} from './IsolatedWorld.js';
import {CdpJSHandle} from './JSHandle.js';
import {
  addPageBinding,
  CDP_BINDING_PREFIX,
  createEvaluationError,
  valueFromPrimitiveRemoteObject,
} from './utils.js';

// rebrowser-patches: isolated world used to look up main-world context ids; one random name per process
const rebrowserLookupWorldName = [...Array(Math.floor(Math.random() * (10 + 1)) + 10)].map(() => Math.random().toString(36)[2]).join('');
let rebrowserFallbackWarned = false;

/**
 * @internal
 */
export class ExecutionContext
  extends EventEmitter<{
    /** Emitted when this execution context is disposed. */
    disposed: undefined;
    consoleapicalled: Protocol.Runtime.ConsoleAPICalledEvent;
    /** Emitted when a binding that is not installed by the ExecutionContext is called. */
    bindingcalled: Protocol.Runtime.BindingCalledEvent;
  }>
  implements Disposable
{
  static #ariaQuerySelectorBinding?: Binding;
  static getOrCreateAriaQuerySelectorBinding(logger: Logger): Binding {
    return (this.#ariaQuerySelectorBinding ??= new Binding(
      '__ariaQuerySelector',
      ARIAQueryHandler.queryOne as (...args: unknown[]) => unknown,
      '', // custom init
      logger,
    ));
  }

  static #ariaQuerySelectorAllBinding?: Binding;
  static getOrCreateAriaQuerySelectorAllBinding(logger: Logger): Binding {
    return (this.#ariaQuerySelectorAllBinding ??= new Binding(
      '__ariaQuerySelectorAll',
      (async (
        element: ElementHandle<Node>,
        selector: string,
      ): Promise<JSHandle<Node[]>> => {
        const results = ARIAQueryHandler.queryAll(element, selector);
        return await element.realm.evaluateHandle(
          (...elements) => {
            return elements;
          },
          ...(await AsyncIterableUtil.collect(results)),
        );
      }) as (...args: unknown[]) => unknown,
      '', // custom init
      logger,
    ));
  }

  #client: CDPSession;
  #world: IsolatedWorld;
  #id: number;
  _frameId: any;
  #name?: string;

  readonly #disposables = new DisposableStack();
  #logger: Logger;

  constructor(
    client: CDPSession,
    contextPayload: Protocol.Runtime.ExecutionContextDescription,
    world: IsolatedWorld,
    logger: Logger,
  ) {
    super(undefined, logger);
    this.#client = client;
    this.#world = world;
    this.#logger = logger;
    this.#id = contextPayload.id;
    if (contextPayload.name) {
      this.#name = contextPayload.name;
    }
    // rebrowser-patches: keep frameId to use later
    if (contextPayload.auxData?.frameId) {
      this._frameId = contextPayload.auxData?.frameId;
    }
    const clientEmitter = this.#disposables.use(new EventEmitter(this.#client));
    clientEmitter.on('Runtime.bindingCalled', this.#onBindingCalled.bind(this));
    if (process.env['REBROWSER_PATCHES_RUNTIME_FIX_MODE'] === '0') {
      clientEmitter.on('Runtime.executionContextDestroyed', async event => {
        if (event.executionContextId === this.#id) {
          this[disposeSymbol]();
        }
      });
      clientEmitter.on('Runtime.executionContextsCleared', async () => {
        this[disposeSymbol]();
      });
    }
    clientEmitter.on('Runtime.consoleAPICalled', this.#onConsoleAPI.bind(this));
    clientEmitter.on(CDPSessionEvent.Disconnected, () => {
      this[disposeSymbol]();
    });
  }

  // Contains mapping from functions that should be bound to Puppeteer functions.
  #bindings = new Map<string, Binding>();

  // If multiple waitFor are set up asynchronously, we need to wait for the
  // first one to set up the binding in the page before running the others.
  #mutex = new Mutex();
  async #addBinding(binding: Binding): Promise<void> {
    if (this.#bindings.has(binding.name)) {
      return;
    }

    using _ = await this.#mutex.acquire();
    try {
      await this.#client.send(
        'Runtime.addBinding',
        this.#name
          ? {
              name: CDP_BINDING_PREFIX + binding.name,
              executionContextName: this.#name,
            }
          : {
              name: CDP_BINDING_PREFIX + binding.name,
              executionContextId: this.#id,
            },
      );

      await this.evaluate(
        addPageBinding,
        'internal',
        binding.name,
        CDP_BINDING_PREFIX,
      );

      this.#bindings.set(binding.name, binding);
    } catch (error) {
      // We could have tried to evaluate in a context which was already
      // destroyed. This happens, for example, if the page is navigated while
      // we are trying to add the binding
      if (error instanceof Error) {
        // Destroyed context.
        if (error.message.includes('Execution context was destroyed')) {
          return;
        }
        // Missing context.
        if (error.message.includes('Cannot find context with specified id')) {
          return;
        }
      }
      this.#logger?.(DEBUG_PREFIXES.error)?.(error);
    }
  }

  async #onBindingCalled(
    event: Protocol.Runtime.BindingCalledEvent,
  ): Promise<void> {
    if (event.executionContextId !== this.#id) {
      // rebrowser-patches: without Runtime events a main world learns its id only when it is first used, so a
      // Puppeteer binding call (JSON payload) may come from it before that. Acquire the id and check again.
      if (
        this.#id !== -1 ||
        process.env['REBROWSER_PATCHES_RUNTIME_FIX_MODE'] === '0' ||
        !event.payload.startsWith('{')
      ) {
        return;
      }
      try {
        await this.acquireContextId();
      } catch {
        return;
      }
      if (event.executionContextId !== this.#id) {
        return;
      }
    }

    let payload: BindingPayload;
    try {
      payload = JSON.parse(event.payload);
    } catch {
      // The binding was either called by something in the page or it was
      // called before our wrapper was initialized.
      return;
    }
    const {type, name, seq, args, isTrivial} = payload;
    if (type !== 'internal') {
      this.emit('bindingcalled', event);
      return;
    }
    if (!this.#bindings.has(name)) {
      this.emit('bindingcalled', event);
      return;
    }

    try {
      const binding = this.#bindings.get(name);
      await binding?.run(this, seq, args, isTrivial);
    } catch (err) {
      this.#logger?.(DEBUG_PREFIXES.error)?.(err);
    }
  }

  get id(): number {
    return this.#id;
  }

  #onConsoleAPI(event: Protocol.Runtime.ConsoleAPICalledEvent): void {
    if (event.executionContextId !== this.#id) {
      return;
    }
    this.emit('consoleapicalled', event);
  }

  #bindingsInstalled = false;
  #puppeteerUtil?: Promise<JSHandle<PuppeteerInjectedUtil>>;
  /**
   * @internal
   */
  get puppeteerUtil(): Promise<JSHandle<PuppeteerInjectedUtil>> {
    let promise = Promise.resolve() as Promise<unknown>;
    if (!this.#bindingsInstalled) {
      promise = Promise.all([
        this.#addBindingWithoutThrowing(
          ExecutionContext.getOrCreateAriaQuerySelectorBinding(this.#logger),
        ),
        this.#addBindingWithoutThrowing(
          ExecutionContext.getOrCreateAriaQuerySelectorAllBinding(this.#logger),
        ),
      ]);
      this.#bindingsInstalled = true;
    }
    scriptInjector.inject(script => {
      if (this.#puppeteerUtil) {
        void this.#puppeteerUtil.then(handle => {
          void handle.dispose();
        });
      }
      this.#puppeteerUtil = promise.then(() => {
        return this.evaluateHandle(script) as Promise<
          JSHandle<PuppeteerInjectedUtil>
        >;
      });
    }, !this.#puppeteerUtil);
    return this.#puppeteerUtil as Promise<JSHandle<PuppeteerInjectedUtil>>;
  }

  async #addBindingWithoutThrowing(binding: Binding) {
    try {
      await this.#addBinding(binding);
    } catch (err) {
      // If the binding cannot be added, the context is broken. We cannot
      // recover so we ignore the error.
      this.#logger?.(DEBUG_PREFIXES.error)?.(err);
    }
  }

  /**
   * Evaluates the given function.
   *
   * @example
   *
   * ```ts
   * const executionContext = await page.mainFrame().executionContext();
   * const result = await executionContext.evaluate(() => Promise.resolve(8 * 7))* ;
   * console.log(result); // prints "56"
   * ```
   *
   * @example
   * A string can also be passed in instead of a function:
   *
   * ```ts
   * console.log(await executionContext.evaluate('1 + 2')); // prints "3"
   * ```
   *
   * @example
   * Handles can also be passed as `args`. They resolve to their referenced object:
   *
   * ```ts
   * const oneHandle = await executionContext.evaluateHandle(() => 1);
   * const twoHandle = await executionContext.evaluateHandle(() => 2);
   * const result = await executionContext.evaluate(
   *   (a, b) => a + b,
   *   oneHandle,
   *   twoHandle,
   * );
   * await oneHandle.dispose();
   * await twoHandle.dispose();
   * console.log(result); // prints '3'.
   * ```
   *
   * @param pageFunction - The function to evaluate.
   * @param args - Additional arguments to pass into the function.
   * @returns The result of evaluating the function. If the result is an object,
   * a vanilla object containing the serializable properties of the result is
   * returned.
   */
  async evaluate<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    pageFunction: Func | string,
    ...args: Params
  ): Promise<Awaited<ReturnType<Func>>> {
    return await this.#evaluate(true, pageFunction, ...args);
  }

  /**
   * Evaluates the given function.
   *
   * Unlike {@link ExecutionContext.evaluate | evaluate}, this method returns a
   * handle to the result of the function.
   *
   * This method may be better suited if the object cannot be serialized (e.g.
   * `Map`) and requires further manipulation.
   *
   * @example
   *
   * ```ts
   * const context = await page.mainFrame().executionContext();
   * const handle: JSHandle<typeof globalThis> = await context.evaluateHandle(
   *   () => Promise.resolve(self),
   * );
   * ```
   *
   * @example
   * A string can also be passed in instead of a function.
   *
   * ```ts
   * const handle: JSHandle<number> = await context.evaluateHandle('1 + 2');
   * ```
   *
   * @example
   * Handles can also be passed as `args`. They resolve to their referenced object:
   *
   * ```ts
   * const bodyHandle: ElementHandle<HTMLBodyElement> =
   *   await context.evaluateHandle(() => {
   *     return document.body;
   *   });
   * const stringHandle: JSHandle<string> = await context.evaluateHandle(
   *   body => body.innerHTML,
   *   body,
   * );
   * console.log(await stringHandle.jsonValue()); // prints body's innerHTML
   * // Always dispose your garbage! :)
   * await bodyHandle.dispose();
   * await stringHandle.dispose();
   * ```
   *
   * @param pageFunction - The function to evaluate.
   * @param args - Additional arguments to pass into the function.
   * @returns A {@link JSHandle | handle} to the result of evaluating the
   * function. If the result is a `Node`, then this will return an
   * {@link ElementHandle | element handle}.
   */
  async evaluateHandle<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    pageFunction: Func | string,
    ...args: Params
  ): Promise<HandleFor<Awaited<ReturnType<Func>>>> {
    return await this.#evaluate(false, pageFunction, ...args);
  }

  // rebrowser-patches: alternative to dispose
  clear(newId: any) {
    this.#id = newId;
    this.#bindings = new Map();
    this.#bindingsInstalled = false;
    this.#puppeteerUtil = undefined;
  }
  async __re__getMainWorld({ client, frameId, isWorker = false }: any) {
    // rebrowser-patches: learn the main world's context id without running anything in the page, so there is
    // nothing for page scripts to notice. Only if that fails (e.g. Chrome changes its object id format), fall back to
    // the binding handshake.
    try {
      const contextId = await this.__re__getMainWorldIdByObject({ client, frameId, isWorker });
      if (contextId)
        return contextId;
    } catch (error) {
      process.env['REBROWSER_PATCHES_DEBUG'] && console.log('[rebrowser-patches][getMainWorld] object lookup failed, using a binding:', error);
    }
    if (!rebrowserFallbackWarned) {
      rebrowserFallbackWarned = true;
      console.warn('[rebrowser-patches] could not look up the page\'s context id without touching the page; falling back to a binding handshake that page scripts can notice. Please report this with your Chrome version. REBROWSER_PATCHES_RUNTIME_FIX_MODE=alwaysIsolated avoids it.');
    }
    return this.__re__getMainWorldByBinding({ client, frameId, isWorker });
  }
  // A worker evaluates `this` in its only context. A frame reads `document` in an isolated world and resolves that
  // node again without a context, which lands in the frame's main world. Either way the remote object id is
  // "<isolate>.<contextId>.<id>".
  async __re__getMainWorldIdByObject({ client, frameId, isWorker }: any) {
    const objectGroup = 'g' + Math.random().toString(36).slice(2);
    let objectId: string | undefined;
    try {
      if (isWorker) {
        objectId = (await client.send('Runtime.evaluate', { expression: 'this', objectGroup })).result.objectId;
      } else {
        const { executionContextId } = await client.send('Page.createIsolatedWorld', { frameId, worldName: rebrowserLookupWorldName, grantUniveralAccess: true });
        const { result } = await client.send('Runtime.evaluate', { expression: 'document', contextId: executionContextId, objectGroup });
        const { node } = await client.send('DOM.describeNode', { objectId: result.objectId });
        objectId = (await client.send('DOM.resolveNode', { backendNodeId: node.backendNodeId, objectGroup })).object.objectId;
      }
    } finally {
      client.send('Runtime.releaseObjectGroup', { objectGroup }).catch(() => {});
    }
    const match = /^-?\d+\.(\d+)\.\d+$/.exec(objectId || '');
    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][getMainWorldIdByObject] frameId = ${frameId}, objectId = ${objectId}`);
    return match ? Number(match[1]) : undefined;
  }
  async __re__getMainWorldByBinding({ client, frameId, isWorker = false }: any) {
    let contextId: any;
    let identifier: any;

    // random name to make it harder to detect for any 3rd party script by watching window object and events
    const randomName = [...Array(Math.floor(Math.random() * (10 + 1)) + 10)].map(() => Math.random().toString(36)[2]).join('');
    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][getMainWorld] binding name = ${randomName}`);

    // add the binding
    await client.send('Runtime.addBinding', {
      name: randomName,
    });

    // listen for 'Runtime.bindingCalled' event
    const bindingCalledHandler = ({ name, payload, executionContextId }: any) => {
      process.env['REBROWSER_PATCHES_DEBUG'] && console.log('[rebrowser-patches][bindingCalledHandler]', {
        name,
        payload,
        executionContextId
      });
      if (contextId > 0) {
        // already acquired the id
        return;
      }
      if (name !== randomName) {
        // ignore irrelevant bindings
        return;
      }
      if (payload !== frameId) {
        // ignore irrelevant frames
        return;
      }
      contextId = executionContextId;
      // remove this listener
      client.off('Runtime.bindingCalled', bindingCalledHandler);
    };
    client.on('Runtime.bindingCalled', bindingCalledHandler);

    if (isWorker) {
      // workers don't support `Page.addScriptToEvaluateOnNewDocument` and `Page.createIsolatedWorld`, but there are no iframes inside of them, so it's safe to just use Runtime.evaluate
      await client.send('Runtime.evaluate', {
        expression: `this['${randomName}']('${frameId}')`,
      });
    } else {
      // we could call the binding right from `addScriptToEvaluateOnNewDocument`, but this way it will be called in all existing frames and it's hard to distinguish children from the parent
      // use `window`, not `self`: pages can reassign `self` (or make it throw, e.g. LavaMoat scuttling), `window` is unforgeable
      ({ identifier } = await client.send('Page.addScriptToEvaluateOnNewDocument', {
        source: `document.addEventListener('${randomName}', (e) => window['${randomName}'](e.detail.frameId))`,
        runImmediately: true,
      }));

      // create new isolated world for this frame
      const createIsolatedWorldResult = await client.send('Page.createIsolatedWorld', {
        frameId,
        // use randomName for worldName to distinguish from normal utility world
        worldName: randomName,
        grantUniveralAccess: true,
      });

      // emit event in the specific frame from the isolated world
      await client.send('Runtime.evaluate', {
        expression: `document.dispatchEvent(new CustomEvent('${randomName}', { detail: { frameId: '${frameId}' } }))`,
        contextId: createIsolatedWorldResult.executionContextId,
      });
    }

    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][getMainWorld] result:`, { contextId });
    // don't leave the handshake behind: a native function with a random name on the global object is easy to spot
    client.send('Runtime.removeBinding', { name: randomName }).catch(() => {});
    if (contextId)
      client.send('Runtime.evaluate', { expression: `delete this['${randomName}']`, contextId }).catch(() => {});
    if (identifier)
      client.send('Page.removeScriptToEvaluateOnNewDocument', { identifier }).catch(() => {});
    return contextId;
  }
  async __re__getIsolatedWorld({ client, frameId, worldName }: any) {
    const createIsolatedWorldResult = await client.send('Page.createIsolatedWorld', {
      frameId,
      worldName,
      grantUniveralAccess: true,
    });
    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][getIsolatedWorld] result:`, createIsolatedWorldResult);
    return createIsolatedWorldResult.executionContextId;
  }
  // rebrowser-patches: get context id if it's missing
  async acquireContextId(tryCount = 1): Promise<any> {
    if (this.#id > 0) {
      return
    }

    const fixMode = process.env['REBROWSER_PATCHES_RUNTIME_FIX_MODE'] || 'addBinding'
    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][acquireContextId] id = ${this.#id}, name = ${this.#name}, fixMode = ${fixMode}, tryCount = ${tryCount}`)

    let contextId: any
    let tryAgain = true;
    let errorMessage = 'N/A'
    if (fixMode === 'addBinding') {
      try {
        if (this.#id === -2) {
          // isolated world
          contextId = await this.__re__getIsolatedWorld({
            client: this.#client,
            frameId: this._frameId,
            worldName: this.#name,
          })
        } else {
          // main world
          contextId = await this.__re__getMainWorld({
            client: this.#client,
            frameId: this._frameId,
            isWorker: this.#id === -3,
          })
        }
      } catch (error: any) {
        process.env['REBROWSER_PATCHES_DEBUG'] && console.error('[rebrowser-patches][acquireContextId] error:', error)
        errorMessage = error.message
        if (error instanceof Error) {
          if (
            error.message.includes('No frame for given id found') ||
            error.message.includes('Target closed') ||
            error.message.includes('Session closed')
          ) {
            // target doesn't exist anymore, don't try again
            tryAgain = false
          }
        }

        this.#logger?.(DEBUG_PREFIXES.error)?.(error);
      }
    } else if (fixMode === 'alwaysIsolated') {
      if (this.#id === -3) {
        throw new Error('[rebrowser-patches] web workers are not supported in alwaysIsolated mode')
      }

      contextId = await this.__re__getIsolatedWorld({
        client: this.#client,
        frameId: this._frameId,
        worldName: this.#name,
      })
    } else if (fixMode === 'enableDisable') {
      const executionContextCreatedHandler = ({ context }: any) => {
        process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][executionContextCreated] this.#id = ${this.#id}, name = ${this.#name}, contextId = ${contextId}, event.context.id = ${context.id}`)

        if (contextId > 0) {
          // already acquired the id
          return
        }

        if (this.#id === -1) {
          // main world of this frame
          if (context.auxData && context.auxData['isDefault'] && context.auxData['frameId'] === this._frameId) {
            contextId = context.id
          }
        } else if (this.#id === -2) {
          // utility world of this frame
          if (this.#name === context.name && context.auxData?.['frameId'] === this._frameId) {
            contextId = context.id
          }
        } else if (this.#id === -3) {
          // web worker
          contextId = context.id
        }
      }

      this.#client.on('Runtime.executionContextCreated', executionContextCreatedHandler)
      await this.#client.send('Runtime.enable')
      await this.#client.send('Runtime.disable')
      this.#client.off('Runtime.executionContextCreated', executionContextCreatedHandler)
    }

    if (!contextId) {
      if (!tryAgain || tryCount >= 3) {
        throw new Error(`[rebrowser-patches] acquireContextId failed (tryAgain = ${tryAgain}, tryCount = ${tryCount}), errorMessage: ${errorMessage}`)
      }
      process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][acquireContextId] failed, try again (tryCount = ${tryCount})`)
      return this.acquireContextId(tryCount + 1)
    }

    this.#id = contextId
  }

  async #evaluate<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    returnByValue: true,
    pageFunction: Func | string,
    ...args: Params
  ): Promise<Awaited<ReturnType<Func>>>;
  async #evaluate<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    returnByValue: false,
    pageFunction: Func | string,
    ...args: Params
  ): Promise<HandleFor<Awaited<ReturnType<Func>>>>;
  async #evaluate<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    returnByValue: boolean,
    pageFunction: Func | string,
    ...args: Params
  ): Promise<HandleFor<Awaited<ReturnType<Func>>> | Awaited<ReturnType<Func>>> {
    // rebrowser-patches: context id is missing, acquire it and try again
    if (this.#id < 0) {
      await this.acquireContextId()
      // @ts-ignore
      return this.#evaluate(returnByValue, pageFunction, ...args)
    }

    const sourceUrlComment = getSourceUrlComment(
      getSourcePuppeteerURLIfAvailable(pageFunction)?.toString() ??
        PuppeteerURL.INTERNAL_URL,
    );

    if (isString(pageFunction)) {
      const contextId = this.#id;
      const expression = pageFunction;
      const expressionWithSourceUrl = SOURCE_URL_REGEX.test(expression)
        ? expression
        : `${expression}\n${sourceUrlComment}\n`;

      const {exceptionDetails, result: remoteObject} = await this.#client
        .send('Runtime.evaluate', {
          expression: expressionWithSourceUrl,
          contextId,
          returnByValue,
          awaitPromise: true,
          userGesture: true,
        })
        .catch(rewriteError);

      if (exceptionDetails) {
        throw createEvaluationError(exceptionDetails);
      }

      if (returnByValue) {
        return valueFromPrimitiveRemoteObject(remoteObject) as HandleFor<
          Awaited<ReturnType<Func>>
        >;
      }

      return this.#world.createCdpHandle(remoteObject) as HandleFor<
        Awaited<ReturnType<Func>>
      >;
    }

    const functionDeclaration = stringifyFunction(pageFunction);
    const functionDeclarationWithSourceUrl = SOURCE_URL_REGEX.test(
      functionDeclaration,
    )
      ? functionDeclaration
      : `${functionDeclaration}\n${sourceUrlComment}\n`;
    let callFunctionOnPromise;
    try {
      callFunctionOnPromise = this.#client.send('Runtime.callFunctionOn', {
        functionDeclaration: functionDeclarationWithSourceUrl,
        executionContextId: this.#id,
        // LazyArgs are used only internally and should not affect the order
        // evaluate calls for the public APIs.
        arguments: args.some(arg => {
          return arg instanceof LazyArg;
        })
          ? await Promise.all(
              args.map(arg => {
                return convertArgumentAsync(this, arg);
              }),
            )
          : args.map(arg => {
              return convertArgument(this, arg);
            }),
        returnByValue,
        awaitPromise: true,
        userGesture: true,
      });
    } catch (error) {
      if (
        error instanceof TypeError &&
        error.message.startsWith('Converting circular structure to JSON')
      ) {
        error.message += ' Recursive objects are not allowed.';
      }
      throw error;
    }
    const {exceptionDetails, result: remoteObject} =
      await callFunctionOnPromise.catch(rewriteError);
    if (exceptionDetails) {
      throw createEvaluationError(exceptionDetails);
    }

    if (returnByValue) {
      return valueFromPrimitiveRemoteObject(
        remoteObject,
      ) as unknown as HandleFor<Awaited<ReturnType<Func>>>;
    }

    return this.#world.createCdpHandle(remoteObject) as HandleFor<
      Awaited<ReturnType<Func>>
    >;

    async function convertArgumentAsync(
      context: ExecutionContext,
      arg: unknown,
    ) {
      if (arg instanceof LazyArg) {
        arg = await arg.get(context);
      }
      return convertArgument(context, arg);
    }

    function convertArgument(
      context: ExecutionContext,
      arg: unknown,
    ): Protocol.Runtime.CallArgument {
      if (typeof arg === 'bigint') {
        return {unserializableValue: `${arg.toString()}n`};
      }
      if (Object.is(arg, -0)) {
        return {unserializableValue: '-0'};
      }
      if (Object.is(arg, Infinity)) {
        return {unserializableValue: 'Infinity'};
      }
      if (Object.is(arg, -Infinity)) {
        return {unserializableValue: '-Infinity'};
      }
      if (Object.is(arg, NaN)) {
        return {unserializableValue: 'NaN'};
      }
      const objectHandle =
        arg && (arg instanceof CdpJSHandle || arg instanceof CdpElementHandle)
          ? arg
          : null;
      if (objectHandle) {
        if (objectHandle.realm !== context.#world) {
          throw new Error(
            'JSHandles can be evaluated only in the context they were created!',
          );
        }
        if (objectHandle.disposed) {
          throw new Error('JSHandle is disposed!');
        }
        if (objectHandle.remoteObject().unserializableValue) {
          return {
            unserializableValue:
              objectHandle.remoteObject().unserializableValue,
          };
        }
        if (!objectHandle.remoteObject().objectId) {
          return {value: objectHandle.remoteObject().value};
        }
        return {objectId: objectHandle.remoteObject().objectId};
      }
      return {value: arg};
    }
  }

  override [disposeSymbol](): void {
    this.#disposables.dispose();
    this.emit('disposed', undefined);
    super[disposeSymbol]();
  }
}

const rewriteError = (error: Error): Protocol.Runtime.EvaluateResponse => {
  if (error.message.includes('Object reference chain is too long')) {
    return {result: {type: 'undefined'}};
  }
  if (error.message.includes("Object couldn't be returned by value")) {
    return {result: {type: 'undefined'}};
  }

  if (
    error.message.endsWith('Cannot find context with specified id') ||
    error.message.endsWith('Inspected target navigated or closed')
  ) {
    throw new Error(
      'Execution context was destroyed, most likely because of a navigation.',
    );
  }
  throw error;
};
