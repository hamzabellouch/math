import OAI.Analysis.IrrationalRotation.Rotation.RotationFields
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem exists_unique_field {θ : ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Circle → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => G x (ξ x)) →
          F =ᵐ[circleMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (algebra_commutes_multiplier θ hT)

end Invariant233.Rotation

end

end OAI
