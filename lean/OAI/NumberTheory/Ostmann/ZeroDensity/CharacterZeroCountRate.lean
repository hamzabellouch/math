import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRightZeroCount

namespace OAI

/-! # Standard conductor-height form of the right-half zero count -/

namespace Ostmann

open scoped BigOperators

theorem character_zero_log_cost (q T : ℝ) (hq : 1 ≤ q) (hT : 0 ≤ T) :
    Real.log (48 * q * (T + 3)) ≤ 8 * Real.log (q * (T + 2)) := by
  have hx : 2 ≤ q * (T + 2) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) hT]
  have hpow : (2 : ℝ) ^ 7 ≤ (q * (T + 2)) ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hy : 48 * q * (T + 3) ≤ 72 * (q * (T + 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) hT]
  have hfinal : 48 * q * (T + 3) ≤ (q * (T + 2)) ^ 8 := by
    calc
      _ ≤ 72 * (q * (T + 2)) := hy
      _ ≤ 2 ^ 7 * (q * (T + 2)) := by nlinarith
      _ ≤ (q * (T + 2)) ^ 7 * (q * (T + 2)) :=
        mul_le_mul_of_nonneg_right hpow (by linarith)
      _ = _ := by ring
  have hl := Real.log_le_log (show 0 < 48 * q * (T + 3) by positivity) hfinal
  simpa [Real.log_pow] using hl

/-- The uniform ordinary zero-count rate on the right half of the critical strip. -/
theorem PrimitiveComplexCharacter.right_zero_sum_rate (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hden : 0 ≤ Real.log (14 / 13 : ℝ) := (Real.log_pos (by norm_num)).le
  calc
    _ ≤ (2 * T + 2) * (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) :=
      χ.right_zero_sum_bound T hT S hS
    _ ≤ (2 * T + 2) * (8 * Real.log ((χ.modulus : ℝ) * (T + 2)) / Real.log (14 / 13)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (character_zero_log_cost _ _ hq hT) hden) (by linarith)
    _ = _ := by ring

end Ostmann

end OAI
