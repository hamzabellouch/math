import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterHadamard
import OAI.NumberTheory.Ostmann.ZeroDensity.LogarithmicGammaBound

namespace OAI

/-! # Logarithmic bounds from the actual character zero sum -/

namespace Ostmann

open Complex

 theorem character_real_zero_sum_nonneg (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) : 0 ≤ characterRealZeroSum χ s := by
  apply tsum_nonneg
  intro i
  rw [realZeroKernel_complex_sub]
  exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip i).2])

theorem character_real_zero_term_le (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i : ℕ) :
    ((s - (actualCharacterZeros χ).zeros i)⁻¹).re ≤ characterRealZeroSum χ s := by
  exact (character_real_zero_summable χ s hs hs2).le_tsum i (fun j _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip j).2]))

theorem exists_character_zero_sum_log_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      characterRealZeroSum χ s ≤ (logDeriv χ.L s).re +
        (1 / 2) * Real.log χ.modulus + B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := characterGamma_logarithmic_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs2
  rw [complex_character_hadamard_identity χ s hs hs2,
    χ.completed_logDeriv_eq_add s hs.le, Complex.add_re]
  have hh := (Complex.re_le_norm _).trans (hb χ s hs hs2)
  linarith

/-- Positivity of every actual zero contribution gives the uniform lower bound
for the ordinary logarithmic derivative used in the zero-free argument. -/
theorem exists_character_logDeriv_real_lower : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      -(1 / 2) * Real.log χ.modulus - B * Real.log (|s.im| + 2) ≤
        (logDeriv χ.L s).re := by
  obtain ⟨B, hB, hb⟩ := exists_character_zero_sum_log_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs2
  have hh := hb χ s hs hs2
  have hn := character_real_zero_sum_nonneg χ s hs
  linarith

end Ostmann

end OAI
