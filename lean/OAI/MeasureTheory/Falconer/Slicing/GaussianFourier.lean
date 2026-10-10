import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! The Gaussian Fourier pairing in the actual ambient dimension. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable def gaussianFourierKernel (n : ℕ) (a : ℂ) (ξ : Space n) : ℂ :=
  ((Real.pi : ℂ) / a) ^ ((n : ℂ) / 2) *
    Complex.exp (-(Real.pi : ℂ)^2 * (‖ξ‖^2 : ℝ) / a)

theorem fourier_gaussian_kernel {n : ℕ} {a : ℂ} (ha : 0 < a.re) (ξ : Space n) :
    𝓕 (fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ))) ξ =
      gaussianFourierKernel n a ξ := by
  simpa [gaussianFourierKernel, Space] using fourier_gaussian_innerProductSpace ha ξ

theorem gaussian_fourier_pairing {n : ℕ} {a : ℂ} (ha : 0 < a.re)
    (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-a * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, gaussianFourierKernel n a ξ * φ ξ := by
  have hgauss : Integrable (fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ))) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add ha 0 (0 : Space n)
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Space n)) (μ := volume) (ν := volume)
    (f := fun x : Space n => Complex.exp (-a * (‖x‖^2 : ℝ)))
    (g := (φ : Space n → ℂ))
    Real.continuous_fourierChar continuous_inner hgauss φ.integrable
  have hflip : (innerₗ (Space n)).flip = innerₗ (Space n) := by
    ext x y
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm _ _
  rw [hflip] at hh
  have he : (∫ x : Space n, Complex.exp (-a * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, 𝓕 (fun x : Space n =>
        Complex.exp (-a * (‖x‖^2 : ℝ))) ξ * φ ξ := by
    simpa only [smul_eq_mul] using! hh.symm
  rw [he]
  simp only [fourier_gaussian_kernel ha]

theorem gaussian_exponential_norm_le_one {a : ℂ} (ha : 0 ≤ a.re)
    {s : ℝ} (hs : 0 ≤ s) : ‖Complex.exp (-(s : ℂ) / a)‖ ≤ 1 := by
  rw [Complex.norm_exp, div_eq_mul_inv, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
  apply Real.exp_le_one_iff.mpr
  have hi : 0 ≤ a⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg ha (Complex.normSq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hi

theorem gaussianFourierKernel_norm_bound {n : ℕ} {a : ℂ} (ha : 0 ≤ a.re)
    {b : ℝ} (hb : 0 < b) (hn : b ≤ ‖a‖) (ξ : Space n) :
    ‖gaussianFourierKernel n a ξ‖ ≤ (Real.pi / b)^((n : ℝ)/2) := by
  have he : -(Real.pi : ℂ)^2 * (‖ξ‖^2 : ℝ) / a =
      -((Real.pi^2 * ‖ξ‖^2 : ℝ) : ℂ) / a := by push_cast; ring
  have hpow : ‖((Real.pi : ℂ) / a)^((n : ℂ)/2)‖ =
      (Real.pi / ‖a‖)^((n : ℝ)/2) := by
    convert Complex.norm_cpow_real ((Real.pi : ℂ)/a) ((n : ℝ)/2) using 1 <;>
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  unfold gaussianFourierKernel
  rw [norm_mul, hpow, he]
  calc
    _ ≤ (Real.pi / ‖a‖)^((n : ℝ)/2) * 1 :=
      mul_le_mul_of_nonneg_left (gaussian_exponential_norm_le_one ha (by positivity))
        (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left Real.pi_pos.le hb hn) (by positivity)

theorem gaussianFourierKernel_damped_bound {n : ℕ} {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (ξ : Space n) :
    ‖gaussianFourierKernel n ((ε : ℂ) + (b : ℂ)*Complex.I) ξ‖ ≤
      (Real.pi / b)^((n : ℝ)/2) := by
  apply gaussianFourierKernel_norm_bound (by simpa using hε) hb
  simpa [abs_of_pos hb] using
    Complex.abs_im_le_norm ((ε : ℂ) + (b : ℂ)*Complex.I)

end Falconer

end OAI
