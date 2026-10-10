import OAI.Probability.SATComputability.WeightedExpressions
import OAI.Probability.SATComputability.SATModel

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators
local instance physicalExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def logTwoExpression : Code := positiveLogExpression .left

theorem logTwoExpression_value : expressionValue logTwoExpression = Real.log 2 := by
  norm_num [logTwoExpression, positiveLogExpression_value, expressionValue]

noncomputable def binaryLogMeanExpression (x y : Code) : Code :=
  logMixtureExpression [(1/2, x), (1/2, y)]

noncomputable def binaryLogSumExpression (x y : Code) : Code :=
  .pair logTwoExpression (binaryLogMeanExpression x y)

@[fun_prop] theorem binaryLogMeanExpression_computable :
    Computable (fun p : Code × Code => binaryLogMeanExpression p.1 p.2) := by
  unfold binaryLogMeanExpression
  fun_prop

@[fun_prop] theorem binaryLogSumExpression_computable :
    Computable (fun p : Code × Code => binaryLogSumExpression p.1 p.2) := by
  unfold binaryLogSumExpression
  fun_prop

theorem binaryLogMeanExpression_value (x y : Code) :
    expressionValue (binaryLogMeanExpression x y) =
      Real.log ((Real.exp (expressionValue x)+Real.exp (expressionValue y))/2) := by
  rw [binaryLogMeanExpression, logMixtureExpression_value]
  · congr 1
    norm_num
    ring
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num
  · norm_num

theorem binaryLogSumExpression_value (x y : Code) :
    expressionValue (binaryLogSumExpression x y) =
      Real.log (Real.exp (expressionValue x)+Real.exp (expressionValue y)) := by
  rw [binaryLogSumExpression, expressionValue, logTwoExpression_value,
    binaryLogMeanExpression_value, Real.log_div (by positivity) (by norm_num)]
  ring

theorem exp_binaryLogSumExpression (x y : Code) :
    Real.exp (expressionValue (binaryLogSumExpression x y)) =
      Real.exp (expressionValue x)+Real.exp (expressionValue y) := by
  rw [binaryLogSumExpression_value, Real.exp_log (by positivity)]

def signedExpression (x : Code) (b : Bool) : Code := if b then x else .rfind' x

@[fun_prop] theorem signedExpression_computable :
    Computable (fun p : Code × Bool => signedExpression p.1 p.2) := by
  unfold signedExpression
  fun_prop

theorem signedExpression_value (x : Code) (b : Bool) :
    expressionValue (signedExpression x b) = expressionValue x * spin b := by
  cases b <;> simp [signedExpression, spin, expressionValue]

noncomputable def logQExpression (x : Code) (b : Bool) : Code :=
  .pair (signedExpression x b) (.rfind' (binaryLogSumExpression (.rfind' x) x))

@[fun_prop] theorem logQExpression_computable :
    Computable (fun p : Code × Bool => logQExpression p.1 p.2) := by
  unfold logQExpression
  fun_prop

theorem exp_logQExpression (x : Code) (b : Bool) :
    Real.exp (expressionValue (logQExpression x b)) = q (expressionValue x) b := by
  have hp : 0 < Real.exp (-expressionValue x)+Real.exp (expressionValue x) := by positivity
  rw [logQExpression, expressionValue, signedExpression_value,
    show expressionValue (.rfind' (binaryLogSumExpression (.rfind' x) x)) =
      -expressionValue (binaryLogSumExpression (.rfind' x) x) from rfl,
    binaryLogSumExpression_value]
  change Real.exp (expressionValue x * spin b +
    -Real.log (Real.exp (-expressionValue x)+Real.exp (expressionValue x))) = _
  rw [← sub_eq_add_neg, Real.exp_sub, Real.exp_log hp]
  simp only [q, Real.cosh_eq]
  congr 1
  ring

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
