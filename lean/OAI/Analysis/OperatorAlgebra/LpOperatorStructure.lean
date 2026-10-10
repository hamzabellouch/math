import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Retype an operator from the abstract Hilbert-space structures to the
canonical L² structures before substituting concrete operator formulas. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness

abbrev HilbertOperatorSpace (K : Type*) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] := K →L[ℂ] K

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def canonicalLpOperator (T : HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ))) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) := T

lemma canonicalLpOperator_apply (T : HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ)))
    (x : Lp H 2 (volume : Measure ℝ)) : canonicalLpOperator T x = T x := rfl

lemma canonicalLpOperator_eq (T : Lp H 2 (volume : Measure ℝ) →L[ℂ]
    Lp H 2 (volume : Measure ℝ)) : canonicalLpOperator T = T := rfl

lemma canonicalLpOperator_mul
    (T U : HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ))) :
    canonicalLpOperator (T * U) = canonicalLpOperator T * canonicalLpOperator U := rfl

end WeakPureInfiniteness

end

end OAI
