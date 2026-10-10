import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OAI.NumberTheory.CubicMoment.Estimates.FourierSmoothing

namespace OAI

/-! Two integrable derivatives give the Fourier L1 bound needed for the
fixed inverse-square extension in the far-cell argument. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

lemma norm_fourier_le_l1 (f : ℝ → ℂ) (x : ℝ) :
    ‖𝓕 f x‖ ≤ ∫ y : ℝ, ‖f y‖ := by
  rw [Real.fourier_eq]
  simpa only [Circle.norm_smul] using norm_integral_le_integral_norm
    (fun y : ℝ => (Real.fourierChar (-inner ℝ y x)) • f y)

lemma fourier_second_deriv (f : ℝ → ℂ) (hf : Integrable f)
    (hdf : Differentiable ℝ f) (hf' : Integrable (deriv f))
    (hdf' : Differentiable ℝ (deriv f)) (hf'' : Integrable (deriv (deriv f))) :
    𝓕 (deriv (deriv f)) = fun x : ℝ => (2*Real.pi*Complex.I*x)^2 • 𝓕 f x := by
  rw [Real.fourier_deriv hf' hdf' hf'',Real.fourier_deriv hf hdf hf']
  funext x
  simp only [smul_smul,pow_two]

lemma fourier_two_derivative_bound (f : ℝ → ℂ) (hf : Integrable f)
    (hdf : Differentiable ℝ f) (hf' : Integrable (deriv f))
    (hdf' : Differentiable ℝ (deriv f)) (hf'' : Integrable (deriv (deriv f))) (x : ℝ) :
    ‖𝓕 f x‖ ≤ ((∫ y : ℝ, ‖f y‖)+
      (∫ y : ℝ, ‖deriv (deriv f) y‖)/(2*Real.pi)^2)/(1+x^2) := by
  have hzero := norm_fourier_le_l1 f x
  have htwo := norm_fourier_le_l1 (deriv (deriv f)) x
  rw [fourier_second_deriv f hf hdf hf' hdf' hf''] at htwo
  have hm : ‖(2*Real.pi*Complex.I*x : ℂ)‖ = 2*Real.pi*|x| := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [norm_smul,norm_pow,hm,mul_pow,mul_pow,sq_abs] at htwo
  have hc : 0 < (2*Real.pi)^2 := by positivity
  have htail : x^2*‖𝓕 f x‖ ≤ (∫ y : ℝ, ‖deriv (deriv f) y‖)/(2*Real.pi)^2 := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [htwo]
  apply (le_div_iff₀ (show 0 < 1+x^2 by positivity)).mpr
  nlinarith only [hzero,htail]

theorem integrable_fourier_of_two_derivatives (f : ℝ → ℂ) (hf : Integrable f)
    (hdf : Differentiable ℝ f) (hf' : Integrable (deriv f))
    (hdf' : Differentiable ℝ (deriv f)) (hf'' : Integrable (deriv (deriv f))) :
    Integrable (𝓕 f) := by
  let M := (∫ y : ℝ, ‖f y‖)+(∫ y : ℝ, ‖deriv (deriv f) y‖)/(2*Real.pi)^2
  have hg : Integrable (fun x : ℝ => M/(1+x^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul M
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply hg.mono' hcont.aestronglyMeasurable
  filter_upwards with x
  exact fourier_two_derivative_bound f hf hdf hf' hdf' hf'' x

/-- Dilation costs no Fourier L1 mass, including the exact Jacobian. -/
theorem fourier_dilation_l1 (f : ℝ → ℂ) {J : ℝ} (hJ : 0 < J) :
    (∫ t : ℝ, ‖𝓕 (fun x => f (J*x)) t‖) = ∫ t : ℝ, ‖𝓕 f t‖ := by
  have he (t : ℝ) : 𝓕 (fun x => f (J*x)) t = (J:ℂ)⁻¹ * 𝓕 f (t/J) := by
    have hmul : 𝓕 (scaledKernel f J) t = (J:ℂ)*𝓕 (fun x => f (J*x)) t := by
      simp only [Real.fourier_real_eq_integral_exp_smul,scaledKernel,smul_eq_mul]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hh := hmul.symm.trans (fourier_scaledKernel f hJ t)
    calc
      _ = (J:ℂ)⁻¹*((J:ℂ)*𝓕 (fun x => f (J*x)) t) := by
        rw [inv_mul_cancel_left₀ (show (J:ℂ) ≠ 0 by exact_mod_cast hJ.ne')]
      _ = _ := by rw [hh]
  simp_rw [he,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hJ.le]
  rw [integral_const_mul]
  have hs := Measure.integral_comp_div (fun t : ℝ => ‖𝓕 f t‖) J
  rw [hs,abs_of_pos hJ,smul_eq_mul]
  field_simp

end CubicFirstMoment

end

end OAI
