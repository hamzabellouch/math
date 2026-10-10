import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterTrigonometric

namespace OAI

/-! # The shifted zero-sum bound from trigonometric positivity -/

namespace Ostmann

open Complex

/-- The coefficient three on the real pole, and the separate doubled-height
pole, give the strict inequality needed to exclude a nonreal exceptional zero. -/
theorem exists_low_height_shifted_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (σ t : ℝ), 1 < σ → σ ≤ 2 → |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
        3 / (σ - 1) + realZeroKernel (σ - 1) (2 * t) +
          2 * Real.log χ.modulus + C := by
  obtain ⟨G, hG, hg⟩ := exists_low_height_zero_sum_error
  obtain ⟨V, hV, hv⟩ := exists_low_height_vonMangoldt_upper
  refine ⟨4 * G + 4 * V, by positivity, ?_⟩
  intro χ σ t hσ hσ2 ht
  have ht2 : |2 * t| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have hzero := hg χ ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
    (by simpa using hσ2) (by simpa using ht.trans (by norm_num : (1 : ℝ) ≤ 2))
  have hreal := hv (σ : ℂ) hσ hσ2 (by simp)
  have hdouble := hv ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
    (by simpa using hσ2) (by simpa using ht2)
  have hp := real_character_trigonometric_sum_nonneg χ σ t hσ
  have he := χ.asComplex.mangoldt_LSeries_eq ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _ at he
  rw [PrimitiveRealCharacter.asComplex_L] at he
  rw [he, neg_div, Complex.neg_re] at hp
  have hk : realZeroKernel (σ - 1) 0 = 1 / (σ - 1) := by
    unfold realZeroKernel
    field_simp [sub_ne_zero.mpr hσ.ne']
    ring
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero] at hdouble hreal
  rw [hk] at hreal
  rw [logDeriv_apply] at hzero
  simp only [div_eq_mul_inv] at *
  linarith

end Ostmann

end OAI
