import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTimeLinearBlend

namespace OAI

/-! The actual nonlinear blend of two agreeing time coordinates has
an invertible derivative when their transverse transition is positive. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def timeCoordinateBlend (g : Base → Base) (χ : Base → ℝ) (x : Base) : Base :=
  (1-χ x) • x + χ x • g x

lemma timeCoordinateBlend_fderiv {g : Base → Base} {χ : Base → ℝ} {p : Base}
    (hg : DifferentiableAt ℝ g p) (hχ : DifferentiableAt ℝ χ p) (hpoint : g p = p) :
    fderiv ℝ (timeCoordinateBlend g χ) p =
      (1-χ p) • ContinuousLinearMap.id ℝ Base + χ p • fderiv ℝ g p := by
  have hD := (((hasFDerivAt_const (1:ℝ) p).sub hχ.hasFDerivAt).smul (hasFDerivAt_id p)).add
    (hχ.hasFDerivAt.smul hg.hasFDerivAt)
  change HasFDerivAt (timeCoordinateBlend g χ) _ p at hD
  rw [hD.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  ext i
  simp [hpoint,smul_eq_mul]
  ring

theorem timeCoordinateBlend_regular {g : Base → Base} {χ : Base → ℝ} {p : Base}
    (hg : DifferentiableAt ℝ g p) (hχ : DifferentiableAt ℝ χ p) (hpoint : g p = p)
    (hsecond : ∀ v, fderiv ℝ g p v 1 = v 1)
    (hfirst : 0 < fderiv ℝ g p ![1,0] 0) (hweight : χ p ∈ Icc (0:ℝ) 1) :
    Function.Bijective (fderiv ℝ (timeCoordinateBlend g χ) p) := by
  rw [timeCoordinateBlend_fderiv hg hχ hpoint]
  exact positive_time_linear_blend _ hsecond hfirst hweight

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
