import OAI.Analysis.IrrationalRotation.Rotation.RotationFields
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields

namespace OAI

open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem exists_unique_field_of_mem_algebra (θ : ℝ)
    (A : Hilbert →L[ℂ] Hilbert) (hA : A ∈ algebra θ) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Hilbert, A f =ᵐ[circleMeasure] fun x => F x (f x)) ∧
      (∀ G : Circle → Fiber →L[ℂ] Fiber,
        (∀ f : Hilbert, A f =ᵐ[circleMeasure] fun x => G x (f x)) →
        F =ᵐ[circleMeasure] G) := by
  exact L2Multiplication.exists_unique_field_of_commutes
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)) A
    (algebra_commutes_multiplier θ hA)

end Invariant233.Rotation

end OAI
