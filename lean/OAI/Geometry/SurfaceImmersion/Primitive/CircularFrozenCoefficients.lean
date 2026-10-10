import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyThreshold

namespace OAI

/-! The first two canonical coefficients depend on the angle value and
fixed geometric data; no derivative of the chosen angle remains. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circularFamilyProfile_frozen_coefficients {Q X Y C e₁ e₂ : E → Vec} {R : E → ℝ}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α (x,t))
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (d : E) :
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 0 =
      frozenSize X Y C R e₁ e₂ (x,α (x,t)) ∧
    profileCoefficients (circularFamilyProfile Q X Y C R e₁ e₂ α d (x,t)) 1 =
      frozenFirst Q X Y C R e₁ e₂ d (x,α (x,t)) := by
  rw [circularFamilyProfile_spatial hQ hR h₁ h₂ hα d]
  refine ⟨rfl,?_⟩
  exact circularSpatialProfile_first _ hQ hR h₁ h₂
    (hα.comp x (differentiableAt_id.prodMk (differentiableAt_const t))) hframe

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
