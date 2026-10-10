import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileNormal

namespace OAI

/-! The scalar limits controlling the boundary argument for a circular
velocity, in the canonical normal frame read from the five profiles. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

def circularBoundaryProfile (X Y C W e₁ e₂ : Vec) (R α β : ℝ) : BoundaryProfile :=
  ![leadingTangent X Y C (R • direction e₁ e₂ α),Y,C,W,
    (R*β) • angularDirection e₁ e₂ α]

lemma circularBoundaryProfile_regular {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    circularBoundaryProfile X Y C W e₁ e₂ R α β ∈ regularBoundaryProfiles := by
  have hYV : Y ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    simp [direction,dotProduct_smul,dotProduct_add,hY₁,hY₂]
  have hCV : C ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    simp [direction,dotProduct_smul,dotProduct_add,hC₁,hC₂]
  have hV : R • direction e₁ e₂ α ≠ 0 := by
    apply smul_ne_zero hR
    intro hh
    have hu := direction_unit h₁ h₂ horth α
    rw [hh] at hu
    norm_num at hu
  exact leading_normal_nondegenerate hD hYV hCV hV

/-- The mixed coefficient agrees in absolute value with the geometric
angular component; the scaled longitudinal coefficient is `R * β`. -/
theorem circularBoundaryProfile_coefficients {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    |profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 2| =
      |W ⬝ᵥ angularDirection e₁ e₂ α| ∧
    |profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 3| = |R*β| := by
  let J := circularBoundaryProfile X Y C W e₁ e₂ R α β
  have hJ : J ∈ regularBoundaryProfiles :=
    circularBoundaryProfile_regular hD hR h₁ h₂ horth hY₁ hY₂ hC₁ hC₂
  let u := angularDirection e₁ e₂ α
  have hu : u ⬝ᵥ u = 1 := angularDirection_unit h₁ h₂ horth α
  have hy : Y ⬝ᵥ u = 0 := angularDirection_perp hY₁ hY₂ α
  have hc : C ⬝ᵥ u = 0 := angularDirection_perp hC₁ hC₂ α
  have hv : u ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    rw [dotProduct_smul,dotProduct_comm u (direction e₁ e₂ α),
      direction_angular_perp h₁ h₂ horth,smul_zero]
  have hx : J 0 ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact dot_leadingTangent_zero ((dotProduct_comm _ _).trans hy)
      ((dotProduct_comm _ _).trans hc) hv
  have hn : profilePreferred J ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact angularDirection_normal_perp R α h₁ h₂ horth hY₁ hY₂ hC₁ hC₂
  have hW := profileComplement_abs_dot hJ hu hx hy hn W
  have hA := profileComplement_abs_dot hJ hu hx hy hn ((R*β) • u)
  refine ⟨hW,?_⟩
  change |((R*β) • u) ⬝ᵥ profileComplement J| = |R*β|
  rw [hA,smul_dotProduct,hu,smul_eq_mul,mul_one]

lemma circularBoundaryProfile_turn_iff {X Y C W e₁ e₂ : Vec} {R α β : ℝ}
    (hD : gramDet Y C ≠ 0) (hR : R ≠ 0)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    profileCoefficients (circularBoundaryProfile X Y C W e₁ e₂ R α β) 3 = 0 ↔ β = 0 := by
  have h := (circularBoundaryProfile_coefficients (X := X) (W := W) (α := α) (β := β) hD hR h₁ h₂ horth hY₁ hY₂ hC₁ hC₂).2
  rw [← abs_eq_zero, h,abs_eq_zero,mul_eq_zero]
  simp [hR]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
