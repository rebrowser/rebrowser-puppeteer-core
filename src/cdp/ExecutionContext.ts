/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

import type {Protocol} from 'devtools-protocol';

import {CDPSessionEvent, type CDPSession} from '../api/CDPSession.js';
import type {ElementHandle} from '../api/ElementHandle.js';
import type {JSHandle} from '../api/JSHandle.js';
import {EventEmitter} from '../common/EventEmitter.js';
import {LazyArg} from '../common/LazyArg.js';
import {scriptInjector} from '../common/ScriptInjector.js';
import type {BindingPayload, EvaluateFunc, HandleFor} from '../common/types.js';
import {
  PuppeteerURL,
  SOURCE_URL_REGEX,
  debugError,
  getSourcePuppeteerURLIfAvailable,
  getSourceUrlComment,
  isString,
} from '../common/util.js';
import type PuppeteerUtil from '../injected/injected.js';
import {AsyncIterableUtil} from '../util/AsyncIterableUtil.js';
import {DisposableStack, disposeSymbol} from '../util/disposable.js';
import {stringifyFunction} from '../util/Function.js';
import {Mutex} from '../util/Mutex.js';

import {ARIAQueryHandler} from './AriaQueryHandler.js';
import {Binding} from './Binding.js';
import {CdpElementHandle} from './ElementHandle.js';
import type {IsolatedWorld} from './IsolatedWorld.js';
import {CdpJSHandle} from './JSHandle.js';
import {
  addPageBinding,
  CDP_BINDING_PREFIX,
  createEvaluationError,
  valueFromRemoteObject,
} from './utils.js';

const ariaQuerySelectorBinding = new Binding(
  '__ariaQuerySelector',
  ARIAQueryHandler.queryOne as (...args: unknown[]) => unknown,
  '' // custom init
);

const ariaQuerySelectorAllBinding = new Binding(
  '__ariaQuerySelectorAll',
  (async (
    element: ElementHandle<Node>,
    selector: string
  ): Promise<JSHandle<Node[]>> => {
    const results = ARIAQueryHandler.queryAll(element, selector);
    return await element.realm.evaluateHandle(
      (...elements) => {
        return elements;
      },
      ...(await AsyncIterableUtil.collect(results))
    );
  }) as (...args: unknown[]) => unknown,
  '' // custom init
);

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
  #client: CDPSession;
  #world: IsolatedWorld;
  #id: number;
  _frameId: any;
  #name?: string;

  readonly #disposables = new DisposableStack();

  constructor(
    client: CDPSession,
    contextPayload: Protocol.Runtime.ExecutionContextDescription,
    world: IsolatedWorld
  ) {
    super();
    this.#client = client;
    this.#world = world;
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
            }
      );

      await this.evaluate(
        addPageBinding,
        'internal',
        binding.name,
        CDP_BINDING_PREFIX
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

      debugError(error);
    }
  }

  async #onBindingCalled(
    event: Protocol.Runtime.BindingCalledEvent
  ): Promise<void> {
    if (event.executionContextId !== this.#id) {
      return;
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
      debugError(err);
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
  #puppeteerUtil?: Promise<JSHandle<PuppeteerUtil>>;
  get puppeteerUtil(): Promise<JSHandle<PuppeteerUtil>> {
    let promise = Promise.resolve() as Promise<unknown>;
    if (!this.#bindingsInstalled) {
      promise = Promise.all([
        this.#addBindingWithoutThrowing(ariaQuerySelectorBinding),
        this.#addBindingWithoutThrowing(ariaQuerySelectorAllBinding),
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
        return this.evaluateHandle(script) as Promise<JSHandle<PuppeteerUtil>>;
      });
    }, !this.#puppeteerUtil);
    return this.#puppeteerUtil as Promise<JSHandle<PuppeteerUtil>>;
  }

  async #addBindingWithoutThrowing(binding: Binding) {
    try {
      await this.#addBinding(binding);
    } catch (err) {
      // If the binding cannot be added, then either the browser doesn't support
      // bindings (e.g. Firefox) or the context is broken. Either breakage is
      // okay, so we ignore the error.
      debugError(err);
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
   *   twoHandle
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
   *   () => Promise.resolve(self)
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
   *   body
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
    this.#id = newId
    this.#bindings = new Map()
    this.#bindingsInstalled = false
    this.#puppeteerUtil = undefined
  }
  // rebrowser-patches: get context id if it's missing
  async acquireContextId() {
    if (this.#id > 0) {
      return
    }

    const fixMode = process.env['REBROWSER_PATCHES_RUNTIME_FIX_MODE'] || 'alwaysIsolated'
    process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][acquireContextId] id = ${this.#id}, name = ${this.#name}, fixMode = ${fixMode}`)

    let contextId: any
    if (fixMode === 'alwaysIsolated') {
      if (this.#id === -3) {
        throw new Error('[rebrowser-patches] web workers are not supported in alwaysIsolated mode')
      }

      const sendRes = await this.#client
        .send('Page.createIsolatedWorld', {
          frameId: this._frameId,
          worldName: this.#name,
          grantUniveralAccess: true,
        })
      process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][acquireContextId] Page.createIsolatedWorld result:`, sendRes)
      contextId = sendRes.executionContextId
    } else if (fixMode === 'enableDisable') {
      const executionContextCreatedHandler = ({ context }: any) => {
        process.env['REBROWSER_PATCHES_DEBUG'] && console.log(`[rebrowser-patches][executionContextCreated] this.#id = ${this.#id}, name = ${this.#name}, contextId = ${contextId}, event.context.id = ${context.id}`)

        if (contextId > 0) {
          // already acquired the id
          return
        }

        if (this.#id === -1) {
          // main world
          if (context.auxData && context.auxData['isDefault']) {
            contextId = context.id
          }
        } else if (this.#id === -2) {
          // utility world
          if (this.#name === context.name) {
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
      throw new Error('[rebrowser-patches] acquireContextId failed')
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
        PuppeteerURL.INTERNAL_URL
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

      return returnByValue
        ? valueFromRemoteObject(remoteObject)
        : this.#world.createCdpHandle(remoteObject);
    }

    const functionDeclaration = stringifyFunction(pageFunction);
    const functionDeclarationWithSourceUrl = SOURCE_URL_REGEX.test(
      functionDeclaration
    )
      ? functionDeclaration
      : `${functionDeclaration}\n${sourceUrlComment}\n`;
    let callFunctionOnPromise;
    try {
      callFunctionOnPromise = this.#client.send('Runtime.callFunctionOn', {
        functionDeclaration: functionDeclarationWithSourceUrl,
        executionContextId: this.#id,
        arguments: args.length
          ? await Promise.all(args.map(convertArgument.bind(this)))
          : [],
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
    return returnByValue
      ? valueFromRemoteObject(remoteObject)
      : this.#world.createCdpHandle(remoteObject);

    async function convertArgument(
      this: ExecutionContext,
      arg: unknown
    ): Promise<Protocol.Runtime.CallArgument> {
      if (arg instanceof LazyArg) {
        arg = await arg.get(this);
      }
      if (typeof arg === 'bigint') {
        // eslint-disable-line valid-typeof
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
        if (objectHandle.realm !== this.#world) {
          throw new Error(
            'JSHandles can be evaluated only in the context they were created!'
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

  [disposeSymbol](): void {
    this.#disposables.dispose();
    this.emit('disposed', undefined);
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
      'Execution context was destroyed, most likely because of a navigation.'
    );
  }
  throw error;
};
