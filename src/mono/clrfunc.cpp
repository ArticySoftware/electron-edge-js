#include "edge.h"

#include "mono/metadata/assembly.h"
#include "mono/metadata/exception.h"
#include "mono/metadata/blob.h"
#include "mono/jit/jit.h"
#include <unordered_map>

#define RETURN_UNDEFINED(scope) return scope.Escape(Nan::Undefined());

#define RETURN_RAWVALUE_OR_UNDEFINED(exc, scope, value) \
if (!*exc) return scope.Escape(value); \
else RETURN_UNDEFINED(scope)

#define RETURN_STRING_OR_UNDEFINED(exc, scope, str) RETURN_RAWVALUE_OR_UNDEFINED(exc, scope, stringCLR2V8(str) )
#define RETURN_VALUE_OR_UNDEFINED(exc, scope, value, type) RETURN_RAWVALUE_OR_UNDEFINED(exc, scope, Nan::New<type>(value).ToLocalChecked() )

#define FNV_PRIME 16777619u
#define FNV_OFFSET_BASIS 2166136261u
namespace Fnv32
{
  /**
  Computes 32 bit FNV hash from a given cstring
  */
  inline unsigned int Compute(const char* data, unsigned int offsetBasis = FNV_OFFSET_BASIS)
  {
    do
    {
      offsetBasis ^= *data;
      offsetBasis *= FNV_PRIME;
    } while (*++data);
    return offsetBasis;
  }
}

struct CacheEntry
{
  public:
    void* Handle;          // Pointer to a MonoClassField (field) or MonoMethod (property)
    const char* Name;      // The name of the field or property

    bool IsField;          // Flag to distinguish between field or property
    bool Hidden;           // true if entry should be skipped
};
std::unordered_map<unsigned int, std::unordered_map<unsigned int, CacheEntry>> classSchemaCache;


ClrFunc::ClrFunc()
{
    // empty
}

ClrFunc::~ClrFunc()
{
    DBG("ClrFunc::~ClrFunc");
    mono_gchandle_free(func);
}

NAN_METHOD(clrFuncProxy)
{
    DBG("clrFuncProxy");
    Nan::HandleScope scope;
    v8::Local<v8::External> correlator = v8::Local<v8::External>::Cast(info[2]);
    ClrFuncWrap* wrap = (ClrFuncWrap*)(correlator->Value());
    ClrFunc* clrFunc = wrap->clrFunc;
    info.GetReturnValue().Set(clrFunc->Call(info[0], info[1]));
}

template<typename T>
void clrFuncProxyNearDeath(const Nan::WeakCallbackInfo<T> &data)
{
    DBG("clrFuncProxyNearDeath");
    ClrFuncWrap* wrap = (ClrFuncWrap*)(data.GetParameter());
    delete wrap->clrFunc;
    wrap->clrFunc = NULL;
    delete wrap;
}

v8::Local<v8::Function> ClrFunc::Initialize(MonoObject* func)
{
    DBG("ClrFunc::Initialize Func<object,Task<object>> wrapper");

    static Nan::Persistent<v8::Function> proxyFactory;
    static Nan::Persistent<v8::Function> proxyFunction;
    v8::Isolate *isolate = v8::Isolate::GetCurrent();
    v8::Local<v8::Context> context = isolate->GetCurrentContext();


    Nan::EscapableHandleScope scope;

    ClrFunc* app = new ClrFunc();
    app->func = mono_gchandle_new(func, FALSE);
    ClrFuncWrap* wrap = new ClrFuncWrap;
    wrap->clrFunc = app;

    // See https://github.com/tjanczuk/edge/issues/128 for context

    if (proxyFactory.IsEmpty())
    {
        v8::Local<v8::Function> clrFuncProxyFunction = Nan::New<v8::FunctionTemplate>(clrFuncProxy)->GetFunction();
        proxyFunction.Reset(clrFuncProxyFunction);
        v8::Local<v8::String> code = Nan::New<v8::String>(
            "(function (f, ctx) { return function (d, cb) { return f(d, cb, ctx); }; })").ToLocalChecked();
        v8::Local<v8::Function> codeFunction =
		    v8::Local<v8::Function>::Cast(
                    v8::Script::Compile(context, code, nullptr).ToLocalChecked()
                    ->Run(context).ToLocalChecked());
        proxyFactory.Reset(codeFunction);
    }

    v8::Local<v8::Value> factoryArgv[] = { Nan::New(proxyFunction), Nan::New<v8::External>((void*)wrap) };
    v8::Local<v8::Function> funcProxy =
        (Nan::Call(Nan::New(proxyFactory), Nan::GetCurrentContext()->Global(), 2, factoryArgv)).ToLocalChecked().As<v8::Function>();
    Nan::Persistent<v8::Function> funcProxyPersistent(funcProxy);
    funcProxyPersistent.SetWeak((void*)wrap, &clrFuncProxyNearDeath, Nan::WeakCallbackType::kParameter);

    return scope.Escape(funcProxy);
}

NAN_METHOD(ClrFunc::Initialize)
{
    DBG("ClrFunc::Initialize MethodInfo wrapper");

    Nan::EscapableHandleScope scope;
    v8::Local<v8::Object> options = info[0]->ToObject();
    v8::Local<v8::Function> result;

    v8::Local<v8::Value> jsassemblyFile = options->Get(Nan::New<v8::String>("assemblyFile").ToLocalChecked());
    if (jsassemblyFile->IsString())
    {
        // reference .NET code through pre-compiled CLR assembly
        String::Utf8Value assemblyFile(jsassemblyFile);
        String::Utf8Value nativeTypeName(options->Get(Nan::New<v8::String>("typeName").ToLocalChecked()));
        String::Utf8Value nativeMethodName(options->Get(Nan::New<v8::String>("methodName").ToLocalChecked()));
        MonoException* exc = NULL;
        MonoObject* func = MonoEmbedding::GetClrFuncReflectionWrapFunc(*assemblyFile, *nativeTypeName, *nativeMethodName, &exc);
        if (exc) {
            return Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
        }
        result = ClrFunc::Initialize(func);
    }
    else
    {
        //// reference .NET code throgh embedded source code that needs to be compiled
        MonoException* exc = NULL;

        String::Utf8Value compilerFile(options->Get(Nan::New<v8::String>("compiler").ToLocalChecked()));
        MonoAssembly *assembly = mono_domain_assembly_open (mono_domain_get(), *compilerFile);
        MonoClass* compilerClass = mono_class_from_name(mono_assembly_get_image(assembly), "", "EdgeCompiler");
        MonoObject* compilerInstance = mono_object_new(mono_domain_get(), compilerClass);
        MonoMethod* ctor = mono_class_get_method_from_name(compilerClass, ".ctor", 0);
        mono_runtime_invoke(ctor, compilerInstance, NULL, (MonoObject**)&exc);
        if (exc) {
            return Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
        }

        MonoMethod* compileFunc = mono_class_get_method_from_name(compilerClass, "CompileFunc", -1);
        MonoReflectionMethod* methodInfo = mono_method_get_object(mono_domain_get(),compileFunc, compilerClass);
        MonoClass* methodBase = mono_class_from_name(mono_get_corlib(), "System.Reflection", "MethodBase");
        MonoMethod* invoke = mono_class_get_method_from_name(methodBase, "Invoke", 2);
        if (compileFunc == NULL)
        {
            // exception
        }
        MonoObject* parameters = ClrFunc::MarshalV8ToCLR(options);
        MonoArray* methodInfoParams = mono_array_new(mono_domain_get(), mono_get_object_class(), 1);
        mono_array_setref(methodInfoParams, 0, parameters);
        void* params[2];
        params[0] = compilerInstance;
        params[1] = methodInfoParams;
        MonoObject* func = mono_runtime_invoke(invoke, methodInfo, params, (MonoObject**)&exc);
        if (exc) {
            return Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
        }

        result = ClrFunc::Initialize(func);
    }

    info.GetReturnValue().Set(result);
}

v8::Local<v8::Value> ClrFunc::MarshalCLRToV8(MonoObject* netdata, MonoException** exc)
{
    DBG("ClrFunc::MarshalCLRToV8");
    Nan::EscapableHandleScope scope;
    v8::Local<v8::Value> jsdata;
    *exc = NULL;

    if (netdata == NULL)
    {
        return scope.Escape(Nan::Null());
    }

    static MonoClass* guid_class;
    static MonoClass* idictionary_class;
    static MonoClass* idictionary_string_object_class;
    static MonoClass* ienumerable_class;
    static MonoClass* datetime_class;
    static MonoClass* uri_class;
    static MonoClass* datetimeoffset_class;
    static MonoMethod* convert_object;
    static bool setup_done = false;

	// fetch class infos once
	if ( !setup_done )
	{
	    if (!guid_class)
	        guid_class = mono_class_from_name (mono_get_corlib(), "System", "Guid");

	    if (!idictionary_class)
	        idictionary_class = mono_class_from_name (mono_get_corlib(), "System.Collections", "IDictionary");

	    if (!idictionary_string_object_class)
	    {
	        idictionary_string_object_class = MonoEmbedding::GetIDictionaryStringObjectClass(exc);
	        if (*exc)
	            ABORT_TODO();
	    }

	    if (!ienumerable_class)
	        ienumerable_class = mono_class_from_name (mono_get_corlib(), "System.Collections", "IEnumerable");

	    if (!datetime_class)
	        datetime_class = mono_class_from_name (mono_get_corlib(), "System", "DateTime");

	    if (!uri_class)
	    {
	        uri_class = MonoEmbedding::GetUriClass(exc);
	        if (*exc)
	            ABORT_TODO();
	    }

	    if (!datetimeoffset_class)
	        datetimeoffset_class = mono_class_from_name (mono_get_corlib(), "System", "DateTimeOffset");

	    if(!convert_object)
	        convert_object = mono_class_get_method_from_name(MonoEmbedding::GetClass(), "ConvertObject", -1);

		setup_done = true;
  	}

	bool converted = false;
	MonoString* primitive = NULL;

	while (true)
	{
		MonoClass* klass = mono_object_get_class(netdata);
		if ( mono_class_is_valuetype(klass) )
		{
			// value types
			MonoType* t = mono_class_get_type(klass);
			switch ( mono_type_get_type(t))
			{
				case MONO_TYPE_BOOLEAN:
					return scope.Escape(Nan::New<v8::Boolean>((bool)*(bool*)mono_object_unbox(netdata)));
				case MONO_TYPE_CHAR:
				{
					MonoString * str = MonoEmbedding::ToString(netdata, exc);
					RETURN_STRING_OR_UNDEFINED(exc, scope, str)
				}
				case MONO_TYPE_I1:
					return scope.Escape(Nan::New<v8::Integer>(*(int8_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_U1:
					return scope.Escape(Nan::New<v8::Integer>(*(uint8_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_I2:
					return scope.Escape(Nan::New<v8::Integer>(*(int16_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_U2:
					return scope.Escape(Nan::New<v8::Integer>(*(uint16_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_I4:
					return scope.Escape(Nan::New<v8::Integer>(*(int32_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_U4:
					return scope.Escape(Nan::New<v8::Integer>(*(uint32_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_R4:
					return scope.Escape(jsdata = Nan::New<v8::Number>(*(float*)mono_object_unbox(netdata)));
				case MONO_TYPE_R8:
					return scope.Escape(jsdata = Nan::New<v8::Number>(*(double*)mono_object_unbox(netdata)));

// add additional cases if we can use BigInt types
#if USE_BIGINT
				case MONO_TYPE_I8:
						return scope.Escape(v8::BigInt::New( v8::Isolate::GetCurrent(), *(int64_t*)mono_object_unbox(netdata)));
				case MONO_TYPE_U8:
						return scope.Escape(v8::BigInt::New( v8::Isolate::GetCurrent(), *(uint64_t*)mono_object_unbox(netdata)));
#endif
				default:
					// handle remaining value types
					if (NULL != (primitive = MonoEmbedding::TryConvertPrimitiveOrDecimal(netdata, exc)) || *exc)
					{
						// decimal, IntPtr, UIntPtr, (long, ulong if not already handled as BigInt)
						RETURN_STRING_OR_UNDEFINED(exc, scope, primitive)
					}
					if (mono_class_is_enum(klass))
					{
						if (enableMarshalEnumAsInt)
						{
							return scope.Escape(Nan::New<v8::Integer>(*(int32_t*)mono_object_unbox(netdata)));
						}
						MonoString* str = MonoEmbedding::ToString(netdata, exc);
						RETURN_STRING_OR_UNDEFINED(exc, scope, str)
					}
					if (klass == guid_class)
					{
						MonoString* str = MonoEmbedding::ToString(netdata, exc);
						RETURN_STRING_OR_UNDEFINED(exc, scope, str)
					}
					if (klass == datetime_class)
					{
						double value = MonoEmbedding::GetDateValue(netdata, exc);
						RETURN_VALUE_OR_UNDEFINED(exc, scope, value, v8::Date)
					}
					if (klass == datetimeoffset_class)
					{
						MonoString* str = MonoEmbedding::ToString(netdata, exc);
						RETURN_STRING_OR_UNDEFINED(exc, scope, str)
					}

					// if not already converted try to convert object
					if (!converted)
					{
						// try to convert object if the method was found
						if ( convert_object )
						{
							void* params[1];
							params[0] = netdata; //obj
							netdata = mono_runtime_invoke(convert_object, NULL, params, NULL);

							DBG("Converter called for value type")
							converted = true;

							// object was converted and type has changed -> go to start
							if (netdata != NULL)
								continue;

							// restore unconverted object pointer and continue
							netdata = (MonoObject*)params[0];
						}
					}

					// if we get here we have a struct without specific handling
					// use property/field iteration on that object
					return scope.Escape(ClrFunc::MarshalCLRObjectToV8(netdata, exc));
			}
		}
		else
		{
			// reference types
			if (klass == mono_get_string_class())
			{
				return scope.Escape(stringCLR2V8((MonoString*)netdata));
			}
			if (mono_class_is_assignable_from(uri_class, klass))
			{
				MonoString* str = MonoEmbedding::ToString(netdata, exc);
				RETURN_STRING_OR_UNDEFINED(exc, scope, str)
			}
			if (mono_class_get_rank(klass) > 0 && mono_class_get_element_class(klass) == mono_get_byte_class())
			{
				MonoArray* buffer = (MonoArray*)netdata;
				size_t length = mono_array_length(buffer);
				if (length > 0)
				{
					uint8_t* pinnedBuffer = mono_array_addr(buffer, uint8_t, 0);
					return scope.Escape(Nan::CopyBuffer((char *)pinnedBuffer, length).ToLocalChecked());
				}
				return scope.Escape(Nan::NewBuffer(0).ToLocalChecked());
			}
			if (mono_class_is_assignable_from(idictionary_string_object_class, klass)
				|| mono_class_is_assignable_from(idictionary_class, klass))
			{
				v8::Local<v8::Object> result = Nan::New<v8::Object>();
				MonoArray* kvs = MonoEmbedding::IDictionaryToFlatArray(netdata, exc);
				if (!*exc)
				{
					size_t length = mono_array_length(kvs);
					for (unsigned int i = 0; i < length && !*exc; i += 2)
					{
						MonoString* k = (MonoString*)mono_array_get(kvs, MonoObject*, i);
						MonoObject* v = mono_array_get(kvs, MonoObject*, i + 1);
						result->Set(
							stringCLR2V8(k),
							ClrFunc::MarshalCLRToV8(v, exc));
					}
					RETURN_RAWVALUE_OR_UNDEFINED(exc, scope, result);
				}
				RETURN_UNDEFINED(scope)
			}
			if (mono_class_is_assignable_from(ienumerable_class, klass))
			{
				v8::Local<v8::Array> result = Nan::New<v8::Array>();
				MonoArray* values = MonoEmbedding::IEnumerableToArray(netdata, exc);
				if (!*exc)
				{
					size_t length = mono_array_length(values);
					unsigned int i = 0;
					for (i = 0; i < length && !*exc; i++)
					{
						MonoObject* value = mono_array_get(values, MonoObject*, i);
						result->Set(i, ClrFunc::MarshalCLRToV8(value, exc));
					}

					RETURN_RAWVALUE_OR_UNDEFINED(exc, scope, result);
				}
				RETURN_UNDEFINED(scope)
			}
			if (MonoEmbedding::GetFuncClass() == klass)
			{
				return scope.Escape(ClrFunc::Initialize(netdata));
			}
			if (mono_class_is_assignable_from(mono_get_exception_class(), klass))
			{
				return scope.Escape(ClrFunc::MarshalCLRExceptionToV8((MonoException*)netdata));
			}

			if (!converted)
			{
				// try to convert object if the method was found
				if (convert_object)
				{
					void* params[1];
					params[0] = netdata; //obj
					netdata = mono_runtime_invoke(convert_object, NULL, params, NULL);

					DBG("Converter called for reference type")
					converted = true;

					// object was converted and type has changed -> go to start
					if (netdata != NULL)
						continue;

					// restore unconverted object pointer and continue
					netdata = (MonoObject*)params[0];
				}
			}

			return scope.Escape( ClrFunc::MarshalCLRObjectToV8(netdata, exc) );
		}
	}
}

v8::Local<v8::Value> ClrFunc::MarshalCLRExceptionToV8(MonoException* exception)
{
    DBG("ClrFunc::MarshalCLRExceptionToV8");
    Nan::EscapableHandleScope scope;
    v8::Local<v8::Object> result;
    v8::Local<v8::String> message;
    v8::Local<v8::String> name;
    MonoException* exc = NULL;

    if (exception == NULL)
    {
        result = Nan::New<v8::Object>();
        message = Nan::New<v8::String>("Unrecognized exception thrown by CLR.").ToLocalChecked();
        name = Nan::New<v8::String>("InternalException").ToLocalChecked();
    }
    else
    {
        MonoEmbedding::NormalizeException(&exception);

        result = ClrFunc::MarshalCLRObjectToV8((MonoObject*)exception, &exc);

        MonoClass* klass = mono_object_get_class((MonoObject*)exception);
        MonoProperty* prop = mono_class_get_property_from_name(klass, "Message");
        message = stringCLR2V8((MonoString*)mono_property_get_value(prop, exception, NULL, NULL));

        char full_name[300];
        snprintf( full_name, 300, "%s.%s", 
        	mono_class_get_namespace(klass), mono_class_get_name(klass));
        	
        //name = stringCLR2V8(mono_string_new_wrapper(full_name));
        name = Nan::New<v8::String>(full_name).ToLocalChecked();
    }

    // Construct an error that is just used for the prototype - not verify efficient
    // but 'typeof Error' should work in JavaScript
    result->SetPrototype(Nan::GetCurrentContext(), v8::Exception::Error(message));
    result->Set(Nan::New<v8::String>("message").ToLocalChecked(), message);

    // Recording the actual type - 'name' seems to be the common used property
    result->Set(Nan::New<v8::String>("name").ToLocalChecked(), name);

    return scope.Escape(result);
}

v8::Local<v8::Object> ClrFunc::MarshalCLRObjectToV8(MonoObject* netdata, MonoException** exc)
{
	// magic numbers taken from metadata/attrdefs.h from mono source code
	static uint32_t MONO_FIELD_ATTR_STATIC = 0x0010;  // static field bit flag
	static uint32_t MONO_FIELD_ATTR_PUBLIC = 0x0006;  // access value for public fields
	static uint32_t MONO_FIELD_ATTR_FIELD_ACCESS_MASK = 0x0007;  // the bit mask to get the field access value

	static uint32_t MONO_METHOD_ATTR_STATIC = 0x0010;  // static property getter bit flag
	static uint32_t MONO_METHOD_ATTR_PUBLIC = 0x0006;  // access value for public methods
	static uint32_t MONO_METHOD_ATTR_ACCESS_MASK = 0x0007;  // the bit mask to get the properties' get method access value

    DBG("ClrFunc::MarshalCLRObjectToV8");
    Nan::EscapableHandleScope scope;
    v8::Local<v8::Object> result = Nan::New<v8::Object>();
    MonoClass* klass = mono_object_get_class(netdata);
    MonoClass* current;
    MonoClassField* field;
    MonoProperty* prop;
    unsigned int hash;
    void* iter = NULL;
    *exc = NULL;

    if ( (0 == strcmp(mono_class_get_name(klass), "MonoType") && 0 == strcmp(mono_class_get_namespace(klass), "System"))
		|| strncmp (mono_class_get_namespace(klass) ,"System.Reflection", 17) == 0)
    {
        // Avoid stack overflow due to self-referencing reflection elements
        return scope.Escape(result);
    }

	// calculate hash over the full qualified class name including namespace
	hash = Fnv32::Compute(mono_class_get_name(klass), Fnv32::Compute(mono_class_get_namespace(klass)));

	// get or create schema info for class
	std::unordered_map<unsigned int, CacheEntry>& classSchema = classSchemaCache[hash];

	// check if we already know the type, otherwise use gather reflection information
	if (classSchema.empty())
	{
		// first time usage of this class, collect field / property information

		for (current = klass; !*exc && current; current = mono_class_get_parent(current))
		{
			iter = NULL;
			while (NULL != (field = mono_class_get_fields(current, &iter)) && !*exc)
			{
				// skip static fields
				if (mono_field_get_flags(field) & MONO_FIELD_ATTR_STATIC)
					continue;

				const char* name = mono_field_get_name(field);
				hash = Fnv32::Compute(name);

				// if we already saw the field in an super class, skip it
				// handles fields with "new" overrides and possibly different visibility
				if (classSchema[hash].Handle)
					continue;

				CacheEntry& entry = classSchema[hash];
				entry.IsField = true;
				entry.Handle = field;
				entry.Name = name;

				// proper check for "public", only using & would also collect "internal" fields
				if ( (mono_field_get_flags(field) & MONO_FIELD_ATTR_FIELD_ACCESS_MASK) != MONO_FIELD_ATTR_PUBLIC )
					entry.Hidden = true;
			}
		}

		// same as above, but now for properties
		for (current = klass; !*exc && current; current = mono_class_get_parent(current))
		{
			iter = NULL;
			while (!*exc && NULL != (prop = mono_class_get_properties(current, &iter)))
			{
				MonoMethod* getMethod = mono_property_get_get_method(prop);
				if (!getMethod)
					continue;	// no get method -> skip

				if (mono_method_get_flags(getMethod, NULL) & MONO_METHOD_ATTR_STATIC)
					continue;	// static property -> skip

				const char* name = mono_property_get_name(prop);
				hash = Fnv32::Compute(name);

				// if we already saw the property in an super class, skip it
				// handles fields with "new" overrides and possibly different visibility
				if (classSchema[hash].Handle)
					continue;

				CacheEntry& entry = classSchema[hash];
				entry.IsField = false;
				entry.Handle = getMethod;
				entry.Name = name;

				// proper check for "public", only using & would also collect "internal" properties
				if ( (mono_method_get_flags(getMethod, NULL) & MONO_METHOD_ATTR_ACCESS_MASK) != MONO_METHOD_ATTR_PUBLIC)
					entry.Hidden = true;
			}
		}
	}

	// value types (structs) need the unboxed value to be able to access properties
	// fields only work with the boxed value.
	bool isValueType = mono_class_is_valuetype(klass);
	void* unboxedValue = isValueType ? mono_object_unbox(netdata) : 0;

	// iterate cached type information
	for (std::unordered_map<unsigned int, CacheEntry>::iterator it = classSchema.begin(); it != classSchema.end(); ++it)
	{
		CacheEntry entry = it->second;
		if (entry.Hidden)
			continue;  // entry is hidden, skip it

		if (entry.IsField)
		{
			// get field value
			MonoObject* value = mono_field_get_value_object(mono_domain_get(), static_cast<MonoClassField*>(entry.Handle), netdata);
			result->Set(
				Nan::New<v8::String>(entry.Name).ToLocalChecked(),
				ClrFunc::MarshalCLRToV8(value, exc));
		}
		else
		{
      		// invoke property get method
			// value types (structs) need the unboxed object to properly access the property values.
			MonoObject* value = mono_runtime_invoke(static_cast<MonoMethod*>(entry.Handle),
				isValueType ? unboxedValue : netdata, NULL, (MonoObject**)exc);
			if (!*exc)
			{
				result->Set(
					Nan::New<v8::String>(entry.Name).ToLocalChecked(),
					ClrFunc::MarshalCLRToV8(value, exc));
			}
		}
	}
    return scope.Escape(result);
}

MonoObject* ClrFunc::MarshalV8ToCLR(v8::Local<v8::Value> jsdata)
{
    DBG("ClrFunc::MarshalV8ToCLR");
    Nan::HandleScope scope;

    if (jsdata->IsFunction())
    {
        NodejsFunc* functionContext = new NodejsFunc(v8::Local<v8::Function>::Cast(jsdata));
        MonoObject* netfunc = functionContext->GetFunc();

        return netfunc;
    }
    else if (node::Buffer::HasInstance(jsdata))
    {
        v8::Local<v8::Object> jsbuffer = jsdata->ToObject();
        MonoArray* netbuffer = mono_array_new(mono_domain_get(), mono_get_byte_class(), (int)node::Buffer::Length(jsbuffer));
        memcpy(mono_array_addr_with_size(netbuffer, sizeof(char), 0), node::Buffer::Data(jsbuffer), mono_array_length(netbuffer));

        return (MonoObject*)netbuffer;
    }
    else if (jsdata->IsArray())
    {
        v8::Local<v8::Array> jsarray = v8::Local<v8::Array>::Cast(jsdata);
        MonoArray* netarray = mono_array_new(mono_domain_get(), mono_get_object_class(), jsarray->Length());
        for (unsigned int i = 0; i < jsarray->Length(); i++)
        {
            mono_array_setref(netarray, i, ClrFunc::MarshalV8ToCLR(jsarray->Get(i)));
        }

        return (MonoObject*)netarray;
    }
    else if (jsdata->IsDate())
    {
        v8::Local<v8::Date> jsdate = v8::Local<v8::Date>::Cast(jsdata);
        double ticks = jsdate->NumberValue();
        return MonoEmbedding::CreateDateTime(ticks);
    }
    else if (jsdata->IsObject())
    {
        MonoObject* netobject = MonoEmbedding::CreateExpandoObject();
        v8::Local<v8::Object> jsobject = v8::Local<v8::Object>::Cast(jsdata);
        v8::Local<v8::Array> propertyNames = jsobject->GetPropertyNames();
        for (unsigned int i = 0; i < propertyNames->Length(); i++)
        {
            v8::Local<v8::String> name = v8::Local<v8::String>::Cast(propertyNames->Get(i));
            v8::String::Utf8Value utf8name(name);
            Dictionary::Add(netobject, *utf8name, ClrFunc::MarshalV8ToCLR(jsobject->Get(name)));
        }

        return netobject;
    }
    else if (jsdata->IsString())
    {
        return (MonoObject*)stringV82CLR(v8::Local<v8::String>::Cast(jsdata));
    }
    else if (jsdata->IsBoolean())
    {
        bool value = jsdata->BooleanValue();
        return mono_value_box(mono_domain_get(), mono_get_boolean_class(), &value);
    }
    else if (jsdata->IsInt32())
    {
        int32_t value = jsdata->Int32Value();
        return mono_value_box(mono_domain_get(), mono_get_int32_class(), &value);
    }
    else if (jsdata->IsUint32())
    {
        uint32_t value = jsdata->Uint32Value();
        return mono_value_box(mono_domain_get(), mono_get_uint32_class(), &value);
    }
#if USE_BIGINT
    else if (jsdata->IsBigInt() )
    {
    	v8::Local<v8::BigInt> bigint = v8::Local<v8::BigInt>::Cast(jsdata);
    	int64_t value = bigint->Int64Value();
	return mono_value_box(mono_domain_get(), mono_get_uint64_class(), &value);
    }
#endif
    else if (jsdata->IsNumber())
    {
        double value = jsdata->NumberValue();
        return mono_value_box(mono_domain_get(), mono_get_double_class(), &value);
    }
    else if (jsdata->IsUndefined() || jsdata->IsNull())
    {
        return NULL;
    }
    else
    {
        ABORT_TODO();
        //throw gcnew System::Exception("Unable to convert V8 value to CLR value.");
    }
}

v8::Local<v8::Value> ClrFunc::Call(v8::Local<v8::Value> payload, v8::Local<v8::Value> callback)
{
    DBG("ClrFunc::Call instance");
    Nan::EscapableHandleScope scope;
    MonoException* exc = NULL;

    ClrFuncInvokeContext* c = new ClrFuncInvokeContext(callback);
    c->Payload(ClrFunc::MarshalV8ToCLR(payload));

    MonoObject* func = mono_gchandle_get_target(this->func);
    void* params[1];
    params[0] = c->Payload();
    MonoMethod* invoke = mono_class_get_method_from_name(mono_object_get_class(func), "Invoke", -1);
    // This is different from dotnet. From the documentation http://www.mono-project.com/Embedding_Mono:
    MonoObject* task = mono_runtime_invoke(invoke, func, params, (MonoObject**)&exc);
    if (exc)
    {
        delete c;
        c = NULL;
        Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
        return scope.Escape(Nan::Undefined());
    }

    MonoProperty* prop = mono_class_get_property_from_name(mono_object_get_class(task), "IsCompleted");
    MonoObject* isCompletedObject = mono_property_get_value(prop, task, NULL, (MonoObject**)&exc);
    if (exc)
    {
        delete c;
        c = NULL;
        Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
        return scope.Escape(Nan::Undefined());
    }

    bool isCompleted = *(bool*)mono_object_unbox(isCompletedObject);
    if (isCompleted)
    {
        // Completed synchronously. Return a value or invoke callback based on call pattern.
        c->Task(task);
        return scope.Escape(c->CompleteOnV8Thread(true));
    }
    else if (c->Sync())
    {
        Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(mono_get_exception_invalid_operation("The JavaScript function was called synchronously "
            "but the underlying CLR function returned without completing the Task. Call the "
            "JavaScript function asynchronously.")));
        return scope.Escape(Nan::Undefined());
    }
    else
    {
        c->InitializeAsyncOperation();

        MonoEmbedding::ContinueTask(task, c->GetMonoObject(), &exc);
        if (exc)
        {
            delete c;
            c = NULL;
            Nan::ThrowError(ClrFunc::MarshalCLRExceptionToV8(exc));
            return scope.Escape(Nan::Undefined());
        }
    }

    return scope.Escape(Nan::Undefined());
}
