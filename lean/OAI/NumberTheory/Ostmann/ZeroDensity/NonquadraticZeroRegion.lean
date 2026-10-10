import OAI.NumberTheory.Ostmann.ZeroDensity.NonquadraticZeroBound
import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroFreeNumerics

namespace OAI

/-! # An unconditional logarithmic zero-free region for nonquadratic characters -/

namespace Ostmann

open Complex

theorem exists_nonquadratic_zero_free_region : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter), χ.character ^ 2 ≠ 1 → ∀ i : ℕ,
      c / (Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1) ≤
        1 - ((actualCharacterZeros χ).zeros i).re := by
  obtain ⟨C, hC, hb⟩ := exists_nonquadratic_zero_sum_bound
  refine ⟨1 / (2000 * (C + 1)), by positivity, ?_⟩
  intro χ hχ i
  let ρ := (actualCharacterZeros χ).zeros i
  let H := Real.log χ.modulus + Real.log (|ρ.im| + 2) + 1
  let δ := 1 / (100 * (C + 1) * H)
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|ρ.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbudget : δ * (C * H) ≤ 1 / 100 := by
    dsimp [δ]
    have he : (1 / (100 * (C + 1) * H)) * (C * H) = C / (100 * (C + 1)) := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcut : (1 / (2000 * (C + 1))) / H = δ / 20 := by
    dsimp [δ]
    field_simp
    ring
  rw [hcut]
  by_contra hnot
  have hnear : 1 - δ / 20 ≤ ρ.re := by dsimp [ρ]; linarith [lt_of_not_ge hnot]
  let a := 1 + δ - ρ.re
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I
  have ha : δ ≤ a := by dsimp [a]; linarith [((actualCharacterZeros χ).in_strip i).2]
  have ha' : a ≤ (21 / 20) * δ := by dsimp [a]; linarith
  have hterm := character_real_zero_term_le χ s (by dsimp [s]; simp; linarith)
    (by dsimp [s]; simp; linarith) i
  have hdiff : s - (actualCharacterZeros χ).zeros i = (a : ℂ) := by
    apply Complex.ext <;> simp [s, a, ρ]
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm
  have hupper := hb χ hχ (1 + δ) ρ.im (by linarith) (by linarith)
  have hup : 4 * characterRealZeroSum χ s ≤ 3 / δ + C * H := by
    simpa only [add_sub_cancel_left] using hupper
  have hp := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 4)).trans hup) hδ.le
  have he : δ * (3 / δ + C * H) = 3 + δ * (C * H) := by field_simp
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  simp only [div_eq_mul_inv] at hm
  linarith

end Ostmann

end OAI
