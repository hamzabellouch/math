import OAI.Combinatorics.EditApproximation.Refinement.ComputedStageParameters

namespace OAI

/-! Exact divisibility and power bounds for the computed time counts. -/

namespace EditApproximation

theorem computed_refinement_count_exact (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (integerParameters N).S * inputSmallLog N ^ 2 = inputHeight N := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpowR := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans
    (inputHeight_polynomial_slack N hN hell)
  have hpow : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpowR
  have hexponent : smallLogExponent N * 2 ≤ heightExponent N := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using hpow
  have hdiv : inputSmallLog N ^ 2 ∣ inputHeight N := by
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using Nat.pow_dvd_pow 2 hexponent
  exact Nat.div_mul_cancel hdiv

theorem computed_refinement_count_real (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    ((integerParameters N).S : ℝ) = (inputHeight N : ℝ) / (inputSmallLog N : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < inputSmallLog N := by exact_mod_cast Nat.two_pow_pos (smallLogExponent N)
  apply (eq_div_iff (pow_ne_zero 2 hpos.ne')).2
  exact_mod_cast computed_refinement_count_exact N hN hell

theorem computed_warmup_count_power (N : ℕ) :
    inputHeight N ^ 3 ≤ (integerParameters N).T ^ 4 ∧
      (integerParameters N).T ^ 4 ≤ 16 * inputHeight N ^ 3 := by
  let k := heightExponent N
  have hlow : 3 * k ≤ ((3 * k + 3) / 4) * 4 := by omega
  have hhigh : ((3 * k + 3) / 4) * 4 ≤ 3 * k + 4 := by omega
  constructor
  · simpa only [integerParameters, inputHeight, ← pow_mul, k, mul_comm] using
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlow
  · have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hhigh
    simpa only [integerParameters, inputHeight, ← pow_mul, pow_add, k,
      show (2 : ℕ) ^ 4 = 16 by norm_num, mul_comm] using h

theorem computed_warmup_count_root (N : ℕ) :
    heightQuarterRoot N ^ 3 ≤ ((integerParameters N).T : ℝ) ∧
      ((integerParameters N).T : ℝ) ≤ 2 * heightQuarterRoot N ^ 3 := by
  have hroot : 0 ≤ heightQuarterRoot N := Real.sqrt_nonneg _
  have hT : (0 : ℝ) ≤ (integerParameters N).T := Nat.cast_nonneg _
  have hpower := computed_warmup_count_power N
  have hlow : (inputHeight N : ℝ) ^ 3 ≤ ((integerParameters N).T : ℝ) ^ 4 := by exact_mod_cast hpower.1
  have hhigh : ((integerParameters N).T : ℝ) ^ 4 ≤ 16 * (inputHeight N : ℝ) ^ 3 := by exact_mod_cast hpower.2
  have hrootPower := heightQuarterRoot_fourth_power N
  constructor
  · apply (pow_le_pow_iff_left₀ (pow_nonneg hroot 3) hT (by decide : 4 ≠ 0)).1
    calc
      (heightQuarterRoot N ^ 3) ^ 4 = (inputHeight N : ℝ) ^ 3 := by
        rw [← pow_mul, Nat.mul_comm 3 4, pow_mul, hrootPower]
      _ ≤ _ := hlow
  · apply (pow_le_pow_iff_left₀ hT (mul_nonneg (by norm_num) (pow_nonneg hroot 3)) (by decide : 4 ≠ 0)).1
    calc
      _ ≤ 16 * (inputHeight N : ℝ) ^ 3 := hhigh
      _ = (2 * heightQuarterRoot N ^ 3) ^ 4 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm 3 4, pow_mul, hrootPower]
        norm_num

end EditApproximation

end OAI
