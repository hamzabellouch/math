import OAI.Analysis.OperatorAlgebra.LpOperatorStructure
import OAI.Analysis.OperatorAlgebra.LpOperatorTensorBound

namespace OAI

/-! Algebraic and norm identities for the canonical L² operator conversion. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma canonicalLpOperator_norm (T : HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ))) :
    ‖canonicalLpOperator T‖ = ‖T‖ := rfl

lemma norm_le_canonicalLpOperator
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    {c : ℝ} (h : c ≤ ‖T‖) : c ≤ ‖canonicalLpOperator T‖ :=
  h.trans_eq (canonicalLpOperator_norm T).symm

lemma canonicalLpOperator_sum {I : Type*} [Fintype I]
    (T : I → HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ))) :
    canonicalLpOperator (∑ i, T i) = ∑ i, canonicalLpOperator (T i) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simp only [canonicalLpOperator_apply, sum_apply]

lemma canonicalLpOperator_tensor_bound [CompleteSpace H] {I : Type*} [Fintype I]
    (l r a b : I → HilbertOperatorSpace (Lp H 2 (volume : Measure ℝ)))
    (h : hilbertOperatorTensorBound l r a b) :
    ‖∑ i, canonicalLpOperator (l i) * canonicalLpOperator (r i)‖ ≤
      ‖∑ i, minimalElementary (canonicalLpOperator (a i))
        (MulOpposite.op (canonicalLpOperator (b i)))‖ := by
  simpa only [canonicalLpOperator_eq] using lp_operator_tensor_bound l r a b h

lemma canonicalLpOperator_sum_bound [CompleteSpace H] {I : Type*} [Fintype I]
    (l r a b : I → Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (h : ‖canonicalLpOperator (∑ i, l i * r i)‖ ≤
      ‖∑ i, minimalElementary (canonicalLpOperator (a i))
        (MulOpposite.op (canonicalLpOperator (b i)))‖) :
    ‖∑ i, l i * r i‖ ≤ ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  simpa only [canonicalLpOperator_eq] using h

end WeakPureInfiniteness

end

end OAI
