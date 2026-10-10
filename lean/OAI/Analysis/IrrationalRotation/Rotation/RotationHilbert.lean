import OAI.Analysis.IrrationalRotation.Model.Rotation
import OAI.Analysis.IrrationalRotation.Operators.HilbertModelSize

namespace OAI

noncomputable section
namespace Invariant233.Rotation

instance hilbert_separable : TopologicalSpace.SeparableSpace Hilbert :=
  HilbertModelSize.circle_representation_separable

theorem hilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ Hilbert :=
  HilbertModelSize.circle_representation_not_finiteDimensional

instance hilbert_nontrivial : Nontrivial Hilbert := by
  cases subsingleton_or_nontrivial Hilbert with
  | inl h =>
    let : Subsingleton Hilbert := h
    exact False.elim (hilbert_not_finiteDimensional inferInstance)
  | inr h => exact h

theorem norm_vacuum : ‖vacuum‖ = 1 := by
  rw [vacuum, MeasureTheory.Lp.norm_const' 2 circleMeasure _ (by norm_num) (by norm_num)]
  simp [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem vacuumFunctional_one : vacuumFunctional 1 = 1 := by
  simp [vacuumFunctional, inner_self_eq_norm_sq_to_K, norm_vacuum]

end Invariant233.Rotation

end

end OAI
