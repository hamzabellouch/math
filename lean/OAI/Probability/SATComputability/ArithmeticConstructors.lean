import OAI.Probability.SATComputability.ArithmeticSyntax

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Encodable Denumerable Nat.Partrec
open scoped BigOperators
local instance arithmeticConstructorsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def rationalExpression (q : ℚ) : Code :=
  .prec .zero (ofNat Code (encode q))

@[fun_prop] theorem rationalExpression_computable : Computable rationalExpression := by
  have : Computable (ofNat Code) := (Primrec.ofNat Code).to_comp
  unfold rationalExpression
  fun_prop

@[simp] theorem rationalExpression_value (q : ℚ) :
    expressionValue (rationalExpression q) = q := by
  simp only [rationalExpression, expressionValue, ite_true, decodedRational,
    encode_ofNat, encodek, Option.getD_some]

def exponentialExpression (e : Code) : Code := .prec .succ e
def positiveLogExpression (e : Code) : Code := .prec .left e
def reciprocalExpression (e : Code) : Code := .prec .right e

@[simp] theorem exponentialExpression_value (e : Code) :
    expressionValue (exponentialExpression e) = Real.exp (expressionValue e) := by
  simp [exponentialExpression, expressionValue]
@[simp] theorem positiveLogExpression_value (e : Code) :
    expressionValue (positiveLogExpression e) = Real.log (max 1 (expressionValue e)) := by
  simp [positiveLogExpression, expressionValue]
@[simp] theorem reciprocalExpression_value (e : Code) :
    expressionValue (reciprocalExpression e) = (max 1 (expressionValue e))⁻¹ := by
  simp [reciprocalExpression, expressionValue]

noncomputable def scaledLogExpression (q : ℚ) (e : Code) : Code :=
  .pair (.rfind' (positiveLogExpression (rationalExpression q⁻¹)))
    (positiveLogExpression (.comp (rationalExpression q⁻¹) e))

theorem scaledLogExpression_value {q : ℚ} {e : Code}
    (hq : 0 < q) (hq1 : q ≤ 1) (he : (q : ℝ) ≤ expressionValue e) :
    expressionValue (scaledLogExpression q e) = Real.log (expressionValue e) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have hi : (1 : ℝ) ≤ (q : ℝ)⁻¹ := (one_le_inv₀ hq').mpr hq1'
  have he' : (1 : ℝ) ≤ (q : ℝ)⁻¹ * expressionValue e := by
    calc
      1 = (q : ℝ)⁻¹ * q := (inv_mul_cancel₀ hq'.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hq'.le)
  simp only [scaledLogExpression, expressionValue, positiveLogExpression_value,
    rationalExpression_value, Rat.cast_inv, max_eq_right hi, max_eq_right he']
  rw [Real.log_mul (inv_ne_zero hq'.ne') (ne_of_gt (hq'.trans_le he))]
  ring

def sumExpressions (es : List Code) : Code := es.foldr Code.pair .zero
def productExpressions (es : List Code) : Code := es.foldr Code.comp .succ

@[fun_prop] theorem sumExpressions_computable : Computable sumExpressions := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const Code.zero)
    ((Code.primrec₂_pair.comp Primrec.fst Primrec.snd).comp Primrec.snd).to₂).to_comp

@[fun_prop] theorem productExpressions_computable : Computable productExpressions := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const Code.succ)
    ((Code.primrec₂_comp.comp Primrec.fst Primrec.snd).comp Primrec.snd).to₂).to_comp

@[simp] theorem sumExpressions_value (es : List Code) :
    expressionValue (sumExpressions es) = (es.map expressionValue).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [sumExpressions, List.foldr_cons, expressionValue,
      List.map_cons, List.sum_cons] using congrArg (expressionValue e + ·) ih

@[simp] theorem productExpressions_value (es : List Code) :
    expressionValue (productExpressions es) = (es.map expressionValue).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [productExpressions, List.foldr_cons, expressionValue,
      List.map_cons, List.prod_cons] using congrArg (expressionValue e * ·) ih

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
