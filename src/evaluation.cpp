/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto &rand : rands) {
        args.push_back(rand->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            ExprType type = primitives[x];
            std::vector<std::string> params;
            Expr body(nullptr);
            if (type == E_VOID) body = Expr(new MakeVoid());
            else if (type == E_EXIT) body = Expr(new Exit());
            else if (type == E_BOOLQ) { params = {"x"}; body = Expr(new IsBoolean(Expr(new Var("x")))); }
            else if (type == E_INTQ) { params = {"x"}; body = Expr(new IsFixnum(Expr(new Var("x")))); }
            else if (type == E_NULLQ) { params = {"x"}; body = Expr(new IsNull(Expr(new Var("x")))); }
            else if (type == E_PAIRQ) { params = {"x"}; body = Expr(new IsPair(Expr(new Var("x")))); }
            else if (type == E_PROCQ) { params = {"x"}; body = Expr(new IsProcedure(Expr(new Var("x")))); }
            else if (type == E_SYMBOLQ) { params = {"x"}; body = Expr(new IsSymbol(Expr(new Var("x")))); }
            else if (type == E_STRINGQ) { params = {"x"}; body = Expr(new IsString(Expr(new Var("x")))); }
            else if (type == E_LISTQ) { params = {"x"}; body = Expr(new IsList(Expr(new Var("x")))); }
            else if (type == E_DISPLAY) { params = {"x"}; body = Expr(new Display(Expr(new Var("x")))); }
            else if (type == E_PLUS) body = Expr(new PlusVar({}));
            else if (type == E_MINUS) body = Expr(new MinusVar({}));
            else if (type == E_MUL) body = Expr(new MultVar({}));
            else if (type == E_DIV) body = Expr(new DivVar({}));
            else if (type == E_MODULO) { params = {"x", "y"}; body = Expr(new Modulo(Expr(new Var("x")), Expr(new Var("y")))); }
            else if (type == E_EXPT) { params = {"x", "y"}; body = Expr(new Expt(Expr(new Var("x")), Expr(new Var("y")))); }
            else if (type == E_EQQ) { params = {"x", "y"}; body = Expr(new IsEq(Expr(new Var("x")), Expr(new Var("y")))); }
            else if (type == E_CONS) { params = {"x", "y"}; body = Expr(new Cons(Expr(new Var("x")), Expr(new Var("y")))); }
            else if (type == E_CAR) { params = {"x"}; body = Expr(new Car(Expr(new Var("x")))); }
            else if (type == E_CDR) { params = {"x"}; body = Expr(new Cdr(Expr(new Var("x")))); }
            else if (type == E_LIST) body = Expr(new ListFunc({}));
            else if (type == E_LT) body = Expr(new LessVar({}));
            else if (type == E_LE) body = Expr(new LessEqVar({}));
            else if (type == E_EQ) body = Expr(new EqualVar({}));
            else if (type == E_GE) body = Expr(new GreaterEqVar({}));
            else if (type == E_GT) body = Expr(new GreaterVar({}));
            else if (type == E_NOT) { params = {"x"}; body = Expr(new Not(Expr(new Var("x")))); }
            
            if (body.get()) return ProcedureV(params, body, empty());
        }
        throw RuntimeError("Variable not found: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n + dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL || rand2->v_type == V_RATIONAL) {
        int n1, d1, n2, d2;
        if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
        else { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
        if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
        else { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
        return RationalV(n1 * d2 + n2 * d1, d1 * d2);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n - dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL || rand2->v_type == V_RATIONAL) {
        int n1, d1, n2, d2;
        if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
        else { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
        if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
        else { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
        return RationalV(n1 * d2 - n2 * d1, d1 * d2);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(rand1.get())->n * dynamic_cast<Integer*>(rand2.get())->n);
    } else if (rand1->v_type == V_RATIONAL || rand2->v_type == V_RATIONAL) {
        int n1, d1, n2, d2;
        if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
        else { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
        if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
        else { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
        return RationalV(n1 * n2, d1 * d2);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    int n1, d1, n2, d2;
    if (rand1->v_type == V_INT) { n1 = dynamic_cast<Integer*>(rand1.get())->n; d1 = 1; }
    else if (rand1->v_type == V_RATIONAL) { n1 = dynamic_cast<Rational*>(rand1.get())->numerator; d1 = dynamic_cast<Rational*>(rand1.get())->denominator; }
    else throw(RuntimeError("Wrong typename"));
    
    if (rand2->v_type == V_INT) { n2 = dynamic_cast<Integer*>(rand2.get())->n; d2 = 1; }
    else if (rand2->v_type == V_RATIONAL) { n2 = dynamic_cast<Rational*>(rand2.get())->numerator; d2 = dynamic_cast<Rational*>(rand2.get())->denominator; }
    else throw(RuntimeError("Wrong typename"));

    if (n2 == 0) throw(RuntimeError("Division by zero"));
    return RationalV(n1 * d2, d1 * n2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    Value res = IntegerV(0);
    Plus p(Expr(nullptr), Expr(nullptr));
    for (const auto& arg : args) {
        res = p.evalRator(res, arg);
    }
    return res;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) throw RuntimeError("minus requires at least one argument");
    Minus m(Expr(nullptr), Expr(nullptr));
    if (args.size() == 1) {
        return m.evalRator(IntegerV(0), args[0]);
    }
    Value res = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        res = m.evalRator(res, args[i]);
    }
    return res;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    Value res = IntegerV(1);
    Mult m(Expr(nullptr), Expr(nullptr));
    for (const auto& arg : args) {
        res = m.evalRator(res, arg);
    }
    return res;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) throw RuntimeError("div requires at least one argument");
    Div d(Expr(nullptr), Expr(nullptr));
    if (args.size() == 1) {
        return d.evalRator(IntegerV(1), args[0]);
    }
    Value res = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        res = d.evalRator(res, args[i]);
    }
    return res;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) > 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) != 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) < 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value res = NullV();
    for (int i = (int)args.size() - 1; i >= 0; --i) {
        res = PairV(args[i], res);
    }
    return res;
}

Value IsList::evalRator(const Value &rand) { // list?
    Value curr = rand;
    while (curr->v_type == V_PAIR) {
        curr = dynamic_cast<Pair*>(curr.get())->cdr;
    }
    return BooleanV(curr->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) throw RuntimeError("car: not a pair");
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) throw RuntimeError("cdr: not a pair");
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-car!: not a pair");
    dynamic_cast<Pair*>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) throw RuntimeError("set-cdr!: not a pair");
    dynamic_cast<Pair*>(rand1.get())->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    Value res = VoidV();
    for (auto &expr : es) {
        res = expr->eval(e);
    }
    return res;
}

static Value convertSyntaxToValue(Syntax s) {
    if (auto n = dynamic_cast<Number*>(s.get())) return IntegerV(n->n);
    if (auto r = dynamic_cast<RationalSyntax*>(s.get())) return RationalV(r->numerator, r->denominator);
    if (auto b = dynamic_cast<TrueSyntax*>(s.get())) return BooleanV(true);
    if (auto b = dynamic_cast<FalseSyntax*>(s.get())) return BooleanV(false);
    if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) return SymbolV(sym->s);
    if (auto str = dynamic_cast<StringSyntax*>(s.get())) return StringV(str->s);
    if (auto lst = dynamic_cast<List*>(s.get())) {
        if (lst->stxs.empty()) return NullV();
        Value res = NullV();
        for (int i = (int)lst->stxs.size() - 1; i >= 0; --i) {
            res = PairV(convertSyntaxToValue(lst->stxs[i]), res);
        }
        return res;
    }
    return VoidV();
}

Value Quote::eval(Assoc& e) {
    return convertSyntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    Value res = BooleanV(true);
    for (auto &rand : rands) {
        res = rand->eval(e);
        if (res->v_type == V_BOOL && !dynamic_cast<Boolean*>(res.get())->b) return res;
    }
    return res;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    for (auto &rand : rands) {
        Value res = rand->eval(e);
        if (!(res->v_type == V_BOOL && !dynamic_cast<Boolean*>(res.get())->b)) return res;
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) return BooleanV(true);
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value c = cond->eval(e);
    if (c->v_type == V_BOOL && !dynamic_cast<Boolean*>(c.get())->b) {
        return alter->eval(e);
    } else {
        return conseq->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (auto &clause : clauses) {
        if (clause.empty()) continue;
        Value c = clause[0]->eval(env);
        if (!(c->v_type == V_BOOL && !dynamic_cast<Boolean*>(c.get())->b)) {
            Value res = VoidV();
            for (size_t i = 1; i < clause.size(); ++i) {
                res = clause[i]->eval(env);
            }
            return res;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) { 
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value r = rator->eval(e);
    if (r->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    Procedure* clos_ptr = dynamic_cast<Procedure*>(r.get());
    
    std::vector<Value> args;
    for (auto &arg_expr : rand) {
        args.push_back(arg_expr->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");
    
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); ++i) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    Value val = e->eval(env);
    if (find(var, env).get() != nullptr) {
        modify(var, val, env);
    } else {
        env = extend(var, val, env);
    }
    return VoidV();
}

Value Let::eval(Assoc &env) {
    Assoc new_env = env;
    std::vector<Value> vals;
    for (auto &b : bind) {
        vals.push_back(b.second->eval(env));
    }
    for (size_t i = 0; i < bind.size(); ++i) {
        new_env = extend(bind[i].first, vals[i], new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    Assoc new_env = env;
    for (auto &b : bind) {
        new_env = extend(b.first, VoidV(), new_env);
    }
    for (auto &b : bind) {
        modify(b.first, b.second->eval(new_env), new_env);
    }
    return body->eval(new_env);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    if (find(var, env).get() == nullptr) throw RuntimeError("set!: undefined variable");
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
