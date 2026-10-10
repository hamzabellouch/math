import OAI.Geometry.SurfaceImmersion.Whitney.ExactCollarInterpolation
import OAI.Geometry.SurfaceImmersion.Geometry.SlowFlatRemainder

namespace OAI

/-! Uniform first-derivative control for the retained collar remainders. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def collarInterpolationRemainder (f g : Base → W) (χ : ℝ → ℝ) (x : Base) : W :=
  collarRemainder f x + χ (x 0) • (collarRemainder g x - collarRemainder f x)

lemma collarInterpolationRemainder_smooth {f g : Base → W} {χ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (collarInterpolationRemainder f g χ) :=
  (collarRemainder_smooth hf).add ((hχ.comp (contDiff_apply ℝ ℝ 0)).smul
    ((collarRemainder_smooth hg).sub (collarRemainder_smooth hf)))

theorem collarInterpolationRemainder_bound {f g : Base → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ρ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ →
      (∀ t, |χ t| ≤ 1) → (∀ t, |t*deriv χ t| ≤ 1) →
      ∀ x ∈ closedBall (0 : Base) ρ,
        ‖fderiv ℝ (collarInterpolationRemainder f g χ) x‖ ≤ D*|x 0| := by
  let R := collarRemainder f
  let S := collarRemainder g - collarRemainder f
  have hR : ContDiff ℝ ∞ R := collarRemainder_smooth hf
  have hS : ContDiff ℝ ∞ S := (collarRemainder_smooth hg).sub hR
  have hS0 : ∀ t, S (crosscapAxis t) = 0 := by
    intro t
    simp only [S,Pi.sub_apply,collarRemainder_axis,sub_zero]
  have hSD : ∀ t, fderiv ℝ S (crosscapAxis t) = 0 := by
    intro t
    rw [show S = collarRemainder g - collarRemainder f from rfl,
      fderiv_sub ((collarRemainder_smooth hg).differentiable (by simp) _)
        (hR.differentiable (by simp) _),collarRemainder_first_jet hg,
      collarRemainder_first_jet hf,sub_zero]
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Base) ρ).exists_bound_of_continuousOn
    ((hR.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Base) ρ).exists_bound_of_continuousOn
    ((hS.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).continuousOn
  let P := ‖(ContinuousLinearMap.proj 0 : Base →L[ℝ] ℝ)‖
  let D := |C| + (1+P)*|B| + 1
  have hP : 0 ≤ P := norm_nonneg _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro χ hχ hχb hχd x hx
  have hfirst : ‖fderiv ℝ R x‖ ≤ |C| * |x 0| :=
    axis_flat_first_bound hR (collarRemainder_first_jet hf)
      (fun y hy => (hC y hy).trans (le_abs_self C)) hx
  have hsecond := slow_flat_remainder_bound hS hχ hS0 hSD (abs_nonneg B)
    (fun y hy => (hB y hy).trans (le_abs_self B)) hχb hχd hx
  have hd := fderiv_add (hR.differentiable (by simp) x)
    (((hχ.comp (contDiff_apply ℝ ℝ 0)).smul hS).differentiable (by simp) x)
  change fderiv ℝ (collarInterpolationRemainder f g χ) x = _ at hd
  rw [hd]
  calc
    _ ≤ ‖fderiv ℝ R x‖ + ‖fderiv ℝ (fun y => χ (y 0) • S y) x‖ := norm_add_le _ _
    _ ≤ |C| * |x 0| + (1+P)*|B| * |x 0| := add_le_add hfirst hsecond
    _ ≤ D*|x 0| := by dsimp [D]; nlinarith [abs_nonneg (x 0)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
