import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem fourier_real_dilate (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    𝓕 (fun r => f (r/a)) x = |a| • 𝓕 f (a*x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_div
    (fun r : ℝ => Complex.exp (↑(-2 * Real.pi * r * (a*x)) * Complex.I) • f r) a
  rw [← h]
  apply integral_congr_ae
  filter_upwards with r
  have he : -2 * Real.pi * (r/a) * (a*x) = -2 * Real.pi * r * x := by field_simp
  rw [he]

noncomputable def sourceInverseKernel (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2*Real.pi)⁻¹ • 𝓕 f (x/(2*Real.pi))

theorem sourceInverseKernel_formula (f : ℝ → ℂ) (x : ℝ) :
    sourceInverseKernel f x = (2*Real.pi)⁻¹ •
      ∫ r, Complex.exp (↑(-x*r) * Complex.I) * f r := by
  rw [sourceInverseKernel, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  have he : -2 * Real.pi * r * (x/(2*Real.pi)) = -x*r := by
    field_simp
  rw [he, smul_eq_mul]

theorem sourceInverseKernel_dilate (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    sourceInverseKernel (fun r => f (r/a)) x = |a| • sourceInverseKernel f (a*x) := by
  rw [sourceInverseKernel, fourier_real_dilate f ha]
  have he : a*(x/(2*Real.pi)) = (a*x)/(2*Real.pi) := by ring
  rw [he, smul_comm]
  rfl

noncomputable def sourceShellSchwartz (n : ℕ) : 𝓢(ℝ, ℂ) :=
  ((sourceShellBand_compact n).toSchwartzMap (sourceShellBand_smooth n)).postcompCLM
    Complex.ofRealCLM

@[simp] theorem sourceShellSchwartz_apply (n : ℕ) (r : ℝ) :
    sourceShellSchwartz n r = (sourceShellBand n r : ℂ) := rfl

noncomputable def sourceShellKernel (n : ℕ) : ℝ → ℂ := sourceInverseKernel (sourceShellSchwartz n)

theorem sourceShellKernel_integrable (n : ℕ) : Integrable (sourceShellKernel n) := by
  have h := ((𝓕 (sourceShellSchwartz n)).integrable.comp_div
    (by positivity : 2*Real.pi ≠ 0)).smul ((2*Real.pi)⁻¹)
  change Integrable (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑(sourceShellSchwartz n)) (x/(2*Real.pi)))
  convert h using 1
  funext x
  rw [Pi.smul_apply, SchwartzMap.fourier_coe]

theorem sourceShellBand_dilate (n : ℕ) (r : ℝ) :
    sourceShellBand n r = sourceShellBand 0 (r/(2:ℝ)^n) := by
  simp only [sourceShellBand, sourceShellLowpass, zero_add, pow_zero, pow_one, div_one]
  congr 1
  rw [pow_succ, div_div]

theorem sourceShellKernel_dilate (n : ℕ) (x : ℝ) :
    sourceShellKernel n x = (2:ℝ)^n • sourceShellKernel 0 ((2:ℝ)^n*x) := by
  have he : (sourceShellSchwartz n : ℝ → ℂ) =
      fun r => sourceShellSchwartz 0 (r/(2:ℝ)^n) := by
    funext r
    simp only [sourceShellSchwartz_apply, sourceShellBand_dilate n r]
  rw [sourceShellKernel, he, sourceInverseKernel_dilate _ (by positivity),
    abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rfl

theorem sourceShellKernel_uniform_L1 (n : ℕ) :
    (∫ x, ‖sourceShellKernel n x‖) = ∫ x, ‖sourceShellKernel 0 x‖ := by
  simp_rw [sourceShellKernel_dilate n, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ)<2^n)]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖sourceShellKernel 0 x‖) ((2:ℝ)^n), smul_eq_mul,
    abs_of_pos (by positivity : (0:ℝ)<(2^n)⁻¹)]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end PlanarFalconer

end OAI
