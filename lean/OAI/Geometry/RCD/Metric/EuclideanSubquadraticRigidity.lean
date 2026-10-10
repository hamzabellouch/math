import OAI.Geometry.RCD.Sobolev.EuclideanBoundedHessian

namespace OAI

/-! # Entire harmonic functions with subquadratic growth are affine

Only an exhausting sequence of positive radii and positive bounds is
needed. This is the Euclidean rigidity step in the transformation blow-up.
-/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_harmonic_affine_of_subquadratic_bounds {n : ℕ} (hn : 0 < n)
    {f : Euclidean n → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f univ)
    (R M : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hM : ∀ k, 0 < M k)
    (hRlim : Tendsto R atTop atTop)
    (hdecay : Tendsto (fun k => M k/(R k)^2) atTop (𝓝 0))
    (hbound : ∀ k x, x ∈ ball 0 (R k) → |f x| ≤ M k) :
    ∀ x, f x = f 0 + fderiv ℝ f 0 x := by
  have hC : ContDiff ℝ 2 f := contDiffOn_univ.mp hf.contDiffOn
  obtain ⟨C,hCpos,hHessian⟩ := euclidean_bounded_harmonic_hessian hn
  have hzero (z : Euclidean n) : fderiv ℝ (fderiv ℝ f) z = 0 := by
    suffices hz : ‖fderiv ℝ (fderiv ℝ f) z‖ = 0 by
      exact (norm_eq_zero (a := fderiv ℝ (fderiv ℝ f) z)).mp hz
    apply le_antisymm _ (norm_nonneg (fderiv ℝ (fderiv ℝ f) z))
    have hl : Tendsto (fun k => C*(M k/(R k)^2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hdecay.const_mul C
    apply ge_of_tendsto hl
    filter_upwards [hRlim.eventually_gt_atTop (2*‖z‖)] with k hk
    have hz : z ∈ ball (0 : Euclidean n) (R k/2) := by
      rw [mem_ball,dist_zero_right]
      linarith
    simpa only [mul_div_assoc] using hHessian f (R k) (M k) (hR k) (hM k) hC
      (hf.mono (subset_univ _)) (hbound k) z hz
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hconstant (x : Euclidean n) : fderiv ℝ f x = fderiv ℝ f 0 :=
    is_const_of_fderiv_eq_zero hdf hzero x 0
  have hd : Differentiable ℝ f := hC.differentiable (by norm_num)
  let g : Euclidean n → ℝ := fun x => f x-fderiv ℝ f 0 x
  have hg : Differentiable ℝ g := hd.sub (fderiv ℝ f 0).differentiable
  have hgzero (x : Euclidean n) : fderiv ℝ g x = 0 := by
    change fderiv ℝ (f-⇑(fderiv ℝ f 0)) x = 0
    rw [fderiv_sub (hd x) ((fderiv ℝ f 0).differentiableAt),
      (fderiv ℝ f 0).fderiv,hconstant,sub_self]
  intro x
  have he := is_const_of_fderiv_eq_zero hg hgzero x 0
  change f x-fderiv ℝ f 0 x = f 0-fderiv ℝ f 0 0 at he
  rw [map_zero,sub_zero] at he
  linarith

end RegularPointCoordinates

end

end OAI
