import OAI.NumberTheory.Ostmann.Construction.WordPeriodBudget
import OAI.NumberTheory.Ostmann.Arithmetic.RangedExpandedWordPairBound

namespace OAI

/-! # The actual range partition cost is polynomial at fixed depth -/

namespace Ostmann

/-- Include the extra root product interval in `D`; the same bound then
covers the normalized reciprocal-product comparison. -/
theorem ranged_word_complexity_le {V : Type*} {n : ℕ}
    (D D' : WordRangeDecoration V n) (B : ℕ) (b d m : ℝ)
    (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m))
    (hD : (D.count : ℝ) ≤ d * (1 + m))
    (hD' : (D'.count : ℝ) ≤ d * (1 + m)) :
    (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1) : ℕ) : ℝ) ≤
      (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) *
        b ^ (n + 1) * (1 + m) ^ (n + 2) := by
  let c : ℝ := 3 * 2 ^ n + 3 * ((2 ^ n - 1 : ℕ) : ℝ)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have h1 : 1 ≤ 1 + m := by linarith
  have hpoly : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * (1 + m) ^ (n + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (n + 1)
  have hcount : c + 2 * ((D.count : ℝ) + D'.count) ≤ (c + 4 * d) * (1 + m) := by
    nlinarith
  push_cast
  change (c + 2 * ((D.count : ℝ) + D'.count)) * (B : ℝ) ^ (n + 1) ≤ _
  calc
    _ ≤ ((c + 4 * d) * (1 + m)) * (b ^ (n + 1) * (1 + m) ^ (n + 1)) :=
      mul_le_mul hcount hpoly (by positivity) (by positivity)
    _ = _ := by rw [show n + 2 = n + 1 + 1 from rfl, pow_succ]; ring

theorem ranged_boolean_partition_le {V : Type*} {n : ℕ}
    (D D' : WordRangeDecoration V n) (B : ℕ) (K m : ℝ)
    (hcost : (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1) : ℕ) : ℝ) ≤
      K * (1 + m) ^ (n + 2)) :
    ((3 ^ (2 * ((((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1))) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) : ℝ) ≤
      Real.exp ((4 * Real.log 3 * K) * (1 + m) ^ (n + 2)) := by
  let r := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
  calc
    _ = Real.exp ((2 * (r + r) : ℕ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_cast
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 4 * Real.log 3 by positivity)
      change (2 * (r + r) : ℕ) * Real.log 3 ≤ _
      change (r : ℝ) ≤ _ at hcost
      change 4 * Real.log 3 * (r : ℝ) ≤ _ at hh
      push_cast
      nlinarith only [hh]

end Ostmann

end OAI
