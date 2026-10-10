import OAI.Analysis.KadisonKastler.GaussianStateKernel

namespace OAI

/-! # Locally uniform bounds for analytic Gaussian kernels -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def gaussianStateKernelDeriv (r : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (2 * (r : ℂ) * ((t : ℂ) - z)) * gaussianStateKernel r z t

theorem gaussianStateKernel_hasDerivAt (r : ℝ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => gaussianStateKernel r w t) (gaussianStateKernelDeriv r z t) z := by
  have h0 : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) z := by
    exact (hasDerivAt_id z).const_sub (t : ℂ)
  have h1 : HasDerivAt (fun w : ℂ => -(r : ℂ) * ((t : ℂ) - w) ^ 2)
      (-(r : ℂ) * (2 * ((t : ℂ) - z) ^ 1 * (-1))) z :=
    (h0.pow 2).const_mul (-(r : ℂ))
  have h : HasDerivAt (fun w : ℂ => -(r : ℂ) * ((t : ℂ) - w) ^ 2)
      (2 * (r : ℂ) * ((t : ℂ) - z)) z := by
    convert h1 using 1; ring
  simpa only [gaussianStateKernel, gaussianStateKernelDeriv, mul_comm] using h.cexp

theorem gaussianStateKernel_local_bound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖gaussianStateKernel r z t‖ ≤
      Real.exp (2 * r * R ^ 2) * Real.exp (-(r / 2) * t ^ 2) := by
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz
  have hr2 : z.re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hre
  have hi2 : z.im ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 him
  have hq : t ^ 2 / 2 - z.re ^ 2 ≤ (t - z.re) ^ 2 := by
    nlinarith [sq_nonneg (t - 2 * z.re)]
  rw [gaussianStateKernel_norm, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hr2 hr.le,
    mul_le_mul_of_nonneg_left hi2 hr.le, mul_le_mul_of_nonneg_left hq hr.le]

theorem gaussianStateKernelDeriv_local_bound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (t : ℝ) :
    ‖gaussianStateKernelDeriv r z t‖ ≤
      (2 * r * Real.exp (2 * r * R ^ 2)) *
        ((|t| + R) * Real.exp (-(r / 2) * t ^ 2)) := by
  have hdist : ‖(t : ℂ) - z‖ ≤ |t| + R := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        add_le_add_right hz ‖(t : ℂ)‖
  have hb := gaussianStateKernel_local_bound hr hR hz t
  rw [gaussianStateKernelDeriv, norm_mul, norm_mul]
  have hc : ‖2 * (r : ℂ)‖ = 2 * r := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [hc]
  calc
    _ ≤ (2 * r * (|t| + R)) *
        (Real.exp (2 * r * R ^ 2) * Real.exp (-(r / 2) * t ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity)) hb
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem gaussianStateKernelDeriv_bound_integrable {r : ℝ} (hr : 0 < r) (R : ℝ) :
    Integrable (fun t : ℝ =>
      (2 * r * Real.exp (2 * r * R ^ 2)) *
        ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))) := by
  have hhalf : 0 < r / 2 := by positivity
  have ht : Integrable (fun t : ℝ => |t| * Real.exp (-(r / 2) * t ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hhalf).norm
  have hc := (integrable_exp_neg_mul_sq hhalf).const_mul R
  convert (ht.add hc).const_mul (2 * r * Real.exp (2 * r * R ^ 2)) using 1
  funext t
  change _ = (2 * r * Real.exp (2 * r * R ^ 2)) *
    (|t| * Real.exp (-(r / 2) * t ^ 2) + R * Real.exp (-(r / 2) * t ^ 2))
  ring

end

end KadisonKastler

end OAI
