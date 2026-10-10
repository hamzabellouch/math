import OAI.MeasureTheory.Falconer.Fourier.SchwartzFourierMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

noncomputable def fourierDerivativeL1 (φ : 𝓢(ℝ,ℂ)) (n : ℕ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)/(2*Real.pi)^n

 theorem fourierDerivativeL1_nonneg (φ : 𝓢(ℝ,ℂ)) (n : ℕ) : 0 ≤ fourierDerivativeL1 φ n := by
  unfold fourierDerivativeL1
  exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

 theorem schwartz_fourier_moment_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ ξ : ℝ, ‖ξ‖^n*‖𝓕 φ ξ‖) ≤
      (fourierDerivativeL1 φ n + fourierDerivativeL1 φ (n+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹ := by
  have hi : Integrable (fun ξ : ℝ => ‖ξ‖^n*‖𝓕 φ ξ‖) := (𝓕 φ).integrable_pow_mul volume n
  rw [← integral_const_mul]
  apply integral_mono hi (integrable_inv_one_add_sq.const_mul _) _
  intro ξ
  have h₀ := schwartz_fourier_weighted_pointwise φ n ξ
  have h₂ := schwartz_fourier_weighted_pointwise φ (n+2) ξ
  have hp : 0 < 1+ξ^2 := by positivity
  dsimp only
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  have he : ‖ξ‖^(n+2)*‖𝓕 φ ξ‖ = (‖ξ‖^n*‖𝓕 φ ξ‖)*ξ^2 := by
    rw [pow_add,Real.norm_eq_abs,sq_abs]
    ring
  rw [he] at h₂
  nlinarith

end PlanarFalconer

end OAI
