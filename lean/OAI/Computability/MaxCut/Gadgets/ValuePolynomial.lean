import Mathlib
import OAI.Computability.MaxCut.Estimates.Put

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open Polynomial

 noncomputable def valuePolynomial : Expr → Polynomial ℕ
  | .const n => C n
  | .arg _ | .length => X
  | .bit _ | .zero _ => 1
  | .add a b => valuePolynomial a+valuePolynomial b
  | .sub a _ => valuePolynomial a
  | .mul a b => valuePolynomial a*valuePolynomial b
  | .sum b f => valuePolynomial b*(valuePolynomial f).comp (X+valuePolynomial b)

 theorem valuePolynomial_eval (e : Expr) (M : ℕ) :
    e.valuePolynomial.eval M = e.valueBudget M := by
  induction e generalizing M <;>
    simp_all [valuePolynomial, valueBudget, Polynomial.eval_comp]

 noncomputable def timePolynomial : Expr → Polynomial ℕ
  | .const n => C (n+1)
  | .arg _ => 5*X+2
  | .length => 5*X+6
  | .bit e => timePolynomial e+3*valuePolynomial e+X+7
  | .add a b | .sub a b => timePolynomial a+timePolynomial b+2*valuePolynomial b+1
  | .mul a b => timePolynomial a+timePolynomial b+
      valuePolynomial b*(5*valuePolynomial a+3)+1+2*valuePolynomial a+1+
      2*(valuePolynomial a*valuePolynomial b)+1
  | .zero a => timePolynomial a+2*valuePolynomial a+2
  | .sum b f => timePolynomial b+valuePolynomial b*
      ((timePolynomial f).comp (X+valuePolynomial b)+
        2*(valuePolynomial f).comp (X+valuePolynomial b)+3)+2*valuePolynomial b+2

 theorem timePolynomial_eval (e : Expr) (M : ℕ) :
    e.timePolynomial.eval M = e.timeBudget M := by
  induction e generalizing M <;>
    simp_all [timePolynomial, timeBudget, valuePolynomial_eval, Polynomial.eval_comp]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
