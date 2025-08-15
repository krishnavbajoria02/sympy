from sympy.assumptions.assume import global_assumptions, AppliedPredicate
from sympy.assumptions.cnf import CNF, EncodedCNF
from sympy.assumptions.ask import Q
from sympy.logic.inference import satisfiable
from sympy.logic.algorithms.euf_theory import EUFUnhandledInput
from sympy.matrices.kind import MatrixKind
from sympy.core.kind import NumberKind
from sympy.core.symbol import Dummy, Symbol
from sympy.utilities.iterables import numbered_symbols
from sympy import Lambda
from sympy.core.singleton import S
from sympy import Eq
from sympy.core.relational import Unequality

# Allowed binary preds
ALLOWED_BIN_PRED = {Q.eq, Q.ne}

def euf_ask(proposition, assumptions=True, context=global_assumptions):
    props = CNF.from_prop(proposition)
    _props = CNF.from_prop(~proposition)

    cnf = CNF.from_prop(assumptions)
    assumptions_enc = EncodedCNF()
    assumptions_enc.from_cnf(cnf)

    context_cnf = CNF()
    if context:
        context_cnf = context_cnf.extend(context)
    assumptions_enc.add_from_cnf(context_cnf)

    return check_satisfiability(props, _props, assumptions_enc)

def check_satisfiability(prop, _prop, factbase):
    sat_true = factbase.copy()
    sat_false = factbase.copy()
    sat_true.add_from_cnf(prop)
    sat_false.add_from_cnf(_prop)

    all_pred, all_exprs = get_all_pred_and_expr_from_enc_cnf(sat_true)
    for pred in all_pred:
        if isinstance(pred, AppliedPredicate):
            if len(pred.arguments) == 1:
                continue
            if pred.function not in ALLOWED_BIN_PRED:
                raise EUFUnhandledInput(f"EUFSolver: {pred} not allowed binary predicate")
        else:
            raise EUFUnhandledInput(f"EUFSolver: unsupported literal {pred}")

    for expr in all_exprs:
        if expr.kind == MatrixKind(NumberKind):
            raise EUFUnhandledInput(f"EUFSolver: {expr} is of MatrixKind")
        if expr == S.NaN:
            raise EUFUnhandledInput("EUFSolver: nan")

    sat_true = _preprocess_euf(sat_true)
    sat_false = _preprocess_euf(sat_false)

    can_be_true = satisfiable(sat_true, use_euf_theory=True) is not False
    can_be_false = satisfiable(sat_false, use_euf_theory=True) is not False

    if can_be_true and can_be_false:
        return None
    if can_be_true and not can_be_false:
        return True
    if not can_be_true and can_be_false:
        return False
    raise ValueError("Inconsistent assumptions")

def _preprocess_euf(enc_cnf):
    """
    Rewrite EncodedCNF so only equalities/disequalities at top level remain.
    Unary predicates become equalities between a curried Lambda and a fresh dummy.
    For binary Q.eq/Q.ne with compound sides, introduce Lambda-to-dummy equalities
    for each compound side and replace the original literal with a relation
    between the dummies. This may expand a clause into multiple clauses via
    distribution: (A | (B & C)) -> (A | B) & (A | C).
    """
    enc_cnf = enc_cnf.copy()
    rev_encoding = {v: k for k, v in enc_cnf.encoding.items()}
    new_enc = {}
    new_data = []

    # Create numbered dummy constants for introduced definitions
    dummies = numbered_symbols("_c", lambda name=None: Dummy(name, finite=True))
    lambda_map = {}

    def _ensure_id(expr):
        if expr not in new_enc:
            new_enc[expr] = len(new_enc) + 1
        return new_enc[expr]

    def _lambda_for_term(term):
        """Curried Lambda for an arbitrary term."""
        vars_sorted = sorted(term.free_symbols, key=lambda s: s.name)
        if not vars_sorted:
            v = Dummy()
            return Lambda(v, term)
        lam = Lambda(tuple(vars_sorted), term)
        return lam if len(vars_sorted) == 1 else lam.curry()

    def _lambda_for_pred(arg, predicate_func):
        """Curried Lambda whose body is predicate_func(arg)."""
        vars_sorted = sorted(arg.free_symbols, key=lambda s: s.name)
        body = predicate_func(arg)
        if not vars_sorted:
            v = Dummy()
            return Lambda(v, body)
        lam = Lambda(tuple(vars_sorted), body)
        return lam if len(vars_sorted) == 1 else lam.curry()

    def _rep_for_term(term):
        """Return (representative, supporting_defs) for a term.
        If term is a Symbol, representative is the term itself, no defs.
        Otherwise create a Lambda(term) = c definition and return c with that def.
        """
        if isinstance(term, Symbol):
            return term, []
        lam = _lambda_for_term(term)
        if lam not in lambda_map:
            lambda_map[lam] = next(dummies)
        rep = lambda_map[lam]
        return rep, [Eq(lam, rep)]

    def _expand_literal(pred, sign):
        """Return a list of Eq/Unequality expressions representing the literal.
        Negation is baked into the operator (no Not around predicates).
        The returned list length > 1 denotes a conjunction to be distributed.
        """
        if isinstance(pred, AppliedPredicate):
            # Unary predicate -> Eq(Lambda(...), c) or Unequality(Lambda(...), c)
            if len(pred.arguments) == 1:
                arg = pred.arguments[0]
                lam = _lambda_for_pred(arg, pred.function)
                if lam not in lambda_map:
                    lambda_map[lam] = next(dummies)
                rep = lambda_map[lam]
                return [Eq(lam, rep)] if sign > 0 else [Unequality(lam, rep)]
            # Binary eq/ne
            if pred.function in ALLOWED_BIN_PRED and len(pred.arguments) == 2:
                left, right = pred.arguments
                left_rep, left_defs = _rep_for_term(left)
                right_rep, right_defs = _rep_for_term(right)
                is_eq = (pred.function == Q.eq)
                if sign < 0:
                    is_eq = not is_eq
                core = Eq(left_rep, right_rep) if is_eq else Unequality(left_rep, right_rep)
                return left_defs + right_defs + [core]
            raise EUFUnhandledInput(f"EUFSolver: not allowed {pred}")
        # Fallback: if somehow a non-predicate slipped through, leave it as is
        return [pred]

    # Process each clause with distribution when a literal expands to a conjunction
    for clause in enc_cnf.data:
        # Collect disjunctive base literals and conjunctive factors
        base_or_exprs = []  # literals that remain singletons
        conj_factors = []   # list of lists (each a conjunction to distribute)
        needs_distribution = False
        for lit in clause:
            if lit == 0:
                # False literal; skip as it doesn't contribute to satisfaction
                continue
            pred = rev_encoding[abs(lit)]
            sign = 1 if lit > 0 else -1
            expanded = _expand_literal(pred, sign)
            if len(expanded) == 1:
                base_or_exprs.append(expanded[0])
            else:
                conj_factors.append(expanded)
                needs_distribution = True

        if not needs_distribution:
            # Simple case: encode the clause as a single disjunction
            if not base_or_exprs and not conj_factors:
                # Original clause was purely false -> preserve as {0}
                new_data.append({0})
                continue
            new_clause = set()
            for expr in base_or_exprs:
                new_clause.add(_ensure_id(expr))
            new_data.append(new_clause)
            continue

        # Distribute: start with one partial clause containing the base OR literals
        partial_clauses = [list(base_or_exprs)]
        for factors in conj_factors:
            new_partials = []
            for base in partial_clauses:
                for expr in factors:
                    new_partials.append(base + [expr])
            partial_clauses = new_partials
        for pclause in partial_clauses:
            new_clause = set()
            for expr in pclause:
                new_clause.add(_ensure_id(expr))
            new_data.append(new_clause)

    return EncodedCNF(new_data, new_enc)

def _make_curried_lambda(expr, func_or_pred=None):
    """
    Create a curried Lambda function.

    If func_or_pred is provided, it's applied to expr first as the body.
    Then variables (free symbols of expr) are bound in sorted order and curried.
    When there are no free symbols, introduce a fresh dummy binder.
    """
    if func_or_pred is not None:
        body = func_or_pred(expr)
        vars_sorted = sorted(expr.free_symbols, key=lambda s: s.name)
        if not vars_sorted:
            v = Dummy()
            return Lambda(v, body)
        lam = Lambda(tuple(vars_sorted), body)
        return lam if len(vars_sorted) == 1 else lam.curry()
    # Term case
    vars_sorted = sorted(expr.free_symbols, key=lambda s: s.name)
    if not vars_sorted:
        v = Dummy()
        return Lambda(v, expr)
    lam = Lambda(tuple(vars_sorted), expr)
    return lam if len(vars_sorted) == 1 else lam.curry()

def get_all_pred_and_expr_from_enc_cnf(enc_cnf):
    all_exprs, all_pred = set(), set()
    for pred in enc_cnf.encoding.keys():
        if isinstance(pred, AppliedPredicate):
            all_pred.add(pred)
            all_exprs.update(pred.arguments)
    return all_pred, all_exprs

