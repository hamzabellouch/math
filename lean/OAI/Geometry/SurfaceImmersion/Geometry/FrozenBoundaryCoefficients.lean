import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.FrozenCircularData
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityTurnDominance

namespace OAI

/-! The canonical profile coefficients have the same fixed bounds and turn
mechanism as the explicit circular velocity used to construct the loop. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def circularSpatialProfile (Q X Y C : E → Vec) (R : E → ℝ)
    (e₁ e₂ : E → Vec) (α : E → ℝ) (β : ℝ) (x d : E) : BoundaryProfile :=
  circularBoundaryProfile (X x) (Y x) (C x)
    (fderiv ℝ (fun y => Q y+R y • direction (e₁ y) (e₂ y) (α y)) x d)
    (e₁ x) (e₂ x) (R x) (α x) β

lemma circularSpatialProfile_size (Q X Y C : E → Vec) (R : E → ℝ)
    (e₁ e₂ : E → Vec) (α : E → ℝ) (β : ℝ) (x d : E) :
    profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 0 =
      frozenSize X Y C R e₁ e₂ (x,α x) := rfl

lemma circularSpatialProfile_first {Q X Y C e₁ e₂ : E → Vec} {R α : E → ℝ}
    {x d : E} (β : ℝ) (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) :
    profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 1 =
      frozenFirst Q X Y C R e₁ e₂ d (x,α x) :=
  actual_first_eq_frozen hQ hR h₁ h₂ hα hframe

/-- Large transverse angular derivative gives a large canonical mixed
coefficient; the threshold uses no derivative of the chosen angular phase. -/
theorem circularSpatialProfile_mixed_dominates {Q X Y C e₁ e₂ : E → Vec}
    {R α : E → ℝ} {x d : E} (β : ℝ) {r B T : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hD : gramDet (Y x) (C x) ≠ 0)
    (hframe : e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
      Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧ Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0)
    (hr : 0 < r) (hRx : r ≤ R x) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hbound : ‖spatialError Q R e₁ e₂ α x d‖ ≤ B)
    (hlarge : (T+4*B+1)/r < fderiv ℝ α x d) :
    T+1 < |profileCoefficients (circularSpatialProfile Q X Y C R e₁ e₂ α β x d) 2| := by
  have hunit := angularDirection_unit hframe.1 hframe.2.1 hframe.2.2.1 (α x)
  have hdom := circular_turn_dominates hQ hR h₁ h₂ hα hunit hr hRx hB hT hbound hlarge
  have he := (circularBoundaryProfile_coefficients (X := X x)
    (W := fderiv ℝ (fun y => Q y+R y • direction (e₁ y) (e₂ y) (α y)) x d)
    (α := α x) (β := β) hD (hr.trans_le hRx).ne'
    hframe.1 hframe.2.1 hframe.2.2.1 hframe.2.2.2.1 hframe.2.2.2.2.2.1
    hframe.2.2.2.2.1 hframe.2.2.2.2.2.2).1
  change T+1 < |profileCoefficients
    (circularBoundaryProfile (X x) (Y x) (C x) _ (e₁ x) (e₂ x) (R x) (α x) β) 2|
  rw [he]
  exact hdom.trans_le (le_abs_self _)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
