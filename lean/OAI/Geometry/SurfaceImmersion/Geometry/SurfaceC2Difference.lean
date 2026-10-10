import OAI.Geometry.SurfaceImmersion.Geometry.LocalQuadraticReplacement

namespace OAI

/-! Converting the global second-order norm estimate into the two actual
derivative estimates used by the crosscap direction map. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surface_second_derivative_sub {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Base) :
    fderiv ℝ (fderiv ℝ (g-f)) x =
      fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (g-f) = fderiv ℝ g-fderiv ℝ f := by
    funext y
    exact fderiv_sub (hg.differentiable (by simp) y) (hf.differentiable (by simp) y)
  rw [he]
  exact fderiv_sub ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma surface_C2_difference {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {ε : ℝ}
    (hbound : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (g-f) x‖ ≤ ε) (x : Base) :
    ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ ε := by
  constructor
  · have h := hbound 1 (by decide) x
    rwa [norm_iteratedFDeriv_one,fderiv_sub (hg.differentiable (by simp) x)
      (hf.differentiable (by simp) x)] at h
  · have h := hbound 2 (by decide) x
    rwa [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one,
      surface_second_derivative_sub hf hg] at h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
