import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Operators.HilbertModelSize

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

instance hilbert_separable : TopologicalSpace.SeparableSpace Hilbert :=
  HilbertModelSize.separable_L2_l2 baseMeasure ℤ

theorem hilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ Hilbert :=
  HilbertModelSize.not_finiteDimensional_L2_l2 baseMeasure ℤ

instance hilbert_nontrivial : Nontrivial Hilbert := by
  cases subsingleton_or_nontrivial Hilbert with
  | inl h =>
    let : Subsingleton Hilbert := h
    exact False.elim (hilbert_not_finiteDimensional inferInstance)
  | inr h => exact h

theorem norm_traceVector : ‖traceVector‖ = 1 := by
  rw [traceVector, MeasureTheory.Lp.norm_const' 2 baseMeasure _ (by norm_num) (by norm_num)]
  simp [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem traceVector_inner_one : inner ℂ traceVector ((1 : Hilbert →L[ℂ] Hilbert) traceVector) = 1 := by
  simp [inner_self_eq_norm_sq_to_K, norm_traceVector]

end Invariant233.ProductModel

end

end OAI
