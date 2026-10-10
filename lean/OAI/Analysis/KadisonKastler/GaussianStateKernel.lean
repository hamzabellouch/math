import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! # Gaussian kernels for analytic smearing of a state-preserving action -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def gaussianStateKernel (r : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(r : ℂ) * ((t : ℂ) - z) ^ 2)

theorem gaussianStateKernel_norm (r : ℝ) (z : ℂ) (t : ℝ) :
    ‖gaussianStateKernel r z t‖ =
      Real.exp (r * z.im ^ 2) * Real.exp (-r * (t - z.re) ^ 2) := by
  rw [gaussianStateKernel, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, Complex.sub_im, Complex.neg_im]
  ring

theorem gaussianStateKernel_integrable {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (gaussianStateKernel r z) := by
  have h := ((integrable_exp_neg_mul_sq hr).comp_sub_right z.re).const_mul
    (Real.exp (r * z.im ^ 2))
  have hc : Continuous (gaussianStateKernel r z) := by
    unfold gaussianStateKernel
    fun_prop
  apply h.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => (gaussianStateKernel_norm r z t).le

theorem gaussianStateKernel_norm_integral (r : ℝ) (z : ℂ) :
    (∫ t : ℝ, ‖gaussianStateKernel r z t‖) =
      Real.exp (r * z.im ^ 2) * Real.sqrt (Real.pi / r) := by
  simp_rw [gaussianStateKernel_norm]
  rw [integral_const_mul]
  congr 1
  calc
    (∫ t : ℝ, Real.exp (-r * (t - z.re) ^ 2)) = ∫ t : ℝ, Real.exp (-r * t ^ 2) :=
      integral_sub_right_eq_self (fun t : ℝ => Real.exp (-r * t ^ 2)) z.re
    _ = _ := integral_gaussian r

theorem gaussianStateKernel_real (r s t : ℝ) :
    gaussianStateKernel r (s : ℂ) t = (Real.exp (-r * (t - s) ^ 2) : ℂ) := by
  rw [gaussianStateKernel, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]

theorem gaussianStateKernel_translate (r : ℝ) (z : ℂ) (s t : ℝ) :
    gaussianStateKernel r (z + s) t = gaussianStateKernel r z (t - s) := by
  unfold gaussianStateKernel
  congr 2
  push_cast
  ring

end

end KadisonKastler

end OAI
