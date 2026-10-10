import OAI.NumberTheory.Ostmann.ZeroDensity.VonMangoldtLogarithmicBound
import OAI.NumberTheory.Ostmann.ZeroDensity.NonquadraticZeroBound

namespace OAI

/-! # The real-character shifted zero sum at every height -/

namespace Ostmann

open Complex

theorem exists_full_height_real_shifted_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (σ t : ℝ), 1 < σ → σ ≤ 2 →
      4 * shiftedRealCharacterZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
        3 / (σ - 1) + realZeroKernel (σ - 1) (2 * t) +
          C * (Real.log χ.modulus + Real.log (|t| + 2) + 1) := by
  obtain ⟨G, hG, hg⟩ := exists_character_zero_sum_log_bound
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_logarithmic_upper
  obtain ⟨R, hR, hr⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * G + 2 * V + 3 * R + 4, by positivity, ?_⟩
  intro χ σ t hσ hσ2
  have hzero := hg χ.asComplex ((σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hreal := (Complex.re_le_norm _).trans (hr σ hσ hσ2)
  have hdouble := hv ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hp := real_character_trigonometric_sum_nonneg χ σ t hσ
  have he := χ.asComplex.mangoldt_LSeries_eq ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _ at he
  rw [PrimitiveRealCharacter.asComplex_L] at he
  rw [he, neg_div, Complex.neg_re] at hp
  change shiftedRealCharacterZeroSum χ _ ≤ (logDeriv χ.L _).re +
    (1 / 2) * Real.log χ.modulus + G * Real.log (|((σ : ℂ) + (t : ℂ) * I).im| + 2) at hzero
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero] at hdouble hzero
  have hlog := mul_le_mul_of_nonneg_left (log_double_abs_height_le t) hV.le
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hGq := mul_nonneg hG.le hq
  have hVq := mul_nonneg hV.le hq
  have hRq := mul_nonneg hR.le hq
  have hRt := mul_nonneg hR.le ht
  simp only [logDeriv_apply] at hzero
  simp only [div_eq_mul_inv] at hreal ⊢
  nlinarith

end Ostmann

end OAI
