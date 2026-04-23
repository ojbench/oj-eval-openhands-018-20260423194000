/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id != nullptr) {
        string op = id->s;
        if (reserved_words.count(op) != 0) {
            ExprType type = reserved_words[op];
            if (type == E_QUOTE) {
                if (stxs.size() != 2) throw RuntimeError("quote requires 1 argument");
                return Expr(new Quote(stxs[1]));
            } else if (type == E_IF) {
                if (stxs.size() != 4) throw RuntimeError("if requires 3 arguments");
                return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
            } else if (type == E_BEGIN) {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); ++i) es.push_back(stxs[i]->parse(env));
                return Expr(new Begin(es));
            } else if (type == E_LAMBDA) {
                if (stxs.size() < 3) throw RuntimeError("lambda requires at least 2 arguments");
                List* params_list = dynamic_cast<List*>(stxs[1].get());
                if (!params_list) throw RuntimeError("lambda parameters must be a list");
                vector<string> params;
                for (auto &p_stx : params_list->stxs) {
                    SymbolSyntax* p_sym = dynamic_cast<SymbolSyntax*>(p_stx.get());
                    if (!p_sym) throw RuntimeError("lambda parameter must be a symbol");
                    params.push_back(p_sym->s);
                }
                vector<Expr> body_es;
                for (size_t i = 2; i < stxs.size(); ++i) body_es.push_back(stxs[i]->parse(env));
                return Expr(new Lambda(params, Expr(new Begin(body_es))));
            } else if (type == E_DEFINE) {
                if (stxs.size() < 3) throw RuntimeError("define requires at least 2 arguments");
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (var_sym) {
                    if (stxs.size() != 3) throw RuntimeError("define variable requires 1 value");
                    return Expr(new Define(var_sym->s, stxs[2]->parse(env)));
                } else {
                    List* func_list = dynamic_cast<List*>(stxs[1].get());
                    if (!func_list || func_list->stxs.empty()) throw RuntimeError("invalid define syntax");
                    SymbolSyntax* func_sym = dynamic_cast<SymbolSyntax*>(func_list->stxs[0].get());
                    if (!func_sym) throw RuntimeError("invalid define syntax");
                    vector<string> params;
                    for (size_t i = 1; i < func_list->stxs.size(); ++i) {
                        SymbolSyntax* p_sym = dynamic_cast<SymbolSyntax*>(func_list->stxs[i].get());
                        if (!p_sym) throw RuntimeError("parameter must be a symbol");
                        params.push_back(p_sym->s);
                    }
                    vector<Expr> body_es;
                    for (size_t i = 2; i < stxs.size(); ++i) body_es.push_back(stxs[i]->parse(env));
                    return Expr(new Define(func_sym->s, Expr(new Lambda(params, Expr(new Begin(body_es))))));
                }
            } else if (type == E_LET) {
                if (stxs.size() < 3) throw RuntimeError("let requires at least 2 arguments");
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) throw RuntimeError("let bindings must be a list");
                vector<pair<string, Expr>> binds;
                for (auto &b_stx : bind_list->stxs) {
                    List* b_list = dynamic_cast<List*>(b_stx.get());
                    if (!b_list || b_list->stxs.size() != 2) throw RuntimeError("invalid let binding");
                    SymbolSyntax* b_sym = dynamic_cast<SymbolSyntax*>(b_list->stxs[0].get());
                    if (!b_sym) throw RuntimeError("let binding variable must be a symbol");
                    binds.push_back({b_sym->s, b_list->stxs[1]->parse(env)});
                }
                vector<Expr> body_es;
                for (size_t i = 2; i < stxs.size(); ++i) body_es.push_back(stxs[i]->parse(env));
                return Expr(new Let(binds, Expr(new Begin(body_es))));
            } else if (type == E_LETREC) {
                if (stxs.size() < 3) throw RuntimeError("letrec requires at least 2 arguments");
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) throw RuntimeError("letrec bindings must be a list");
                vector<pair<string, Expr>> binds;
                for (auto &b_stx : bind_list->stxs) {
                    List* b_list = dynamic_cast<List*>(b_stx.get());
                    if (!b_list || b_list->stxs.size() != 2) throw RuntimeError("invalid letrec binding");
                    SymbolSyntax* b_sym = dynamic_cast<SymbolSyntax*>(b_list->stxs[0].get());
                    if (!b_sym) throw RuntimeError("letrec binding variable must be a symbol");
                    binds.push_back({b_sym->s, b_list->stxs[1]->parse(env)});
                }
                vector<Expr> body_es;
                for (size_t i = 2; i < stxs.size(); ++i) body_es.push_back(stxs[i]->parse(env));
                return Expr(new Letrec(binds, Expr(new Begin(body_es))));
            } else if (type == E_COND) {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    List* c_list = dynamic_cast<List*>(stxs[i].get());
                    if (!c_list || c_list->stxs.empty()) throw RuntimeError("invalid cond clause");
                    vector<Expr> clause;
                    for (auto &c_stx : c_list->stxs) clause.push_back(c_stx->parse(env));
                    clauses.push_back(clause);
                }
                return Expr(new Cond(clauses));
            } else if (type == E_SET) {
                if (stxs.size() != 3) throw RuntimeError("set! requires 2 arguments");
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var_sym) throw RuntimeError("set! variable must be a symbol");
                return Expr(new Set(var_sym->s, stxs[2]->parse(env)));
            }
        }
    }

    // Default: function application
    Expr rator = stxs[0]->parse(env);
    vector<Expr> rands;
    for (size_t i = 1; i < stxs.size(); ++i) rands.push_back(stxs[i]->parse(env));
    return Expr(new Apply(rator, rands));
}
