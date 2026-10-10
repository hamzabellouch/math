import OAI.Combinatorics.Sensitivity.ComparisonSequences

namespace OAI

/-! The explicit finite-depth error fraction. -/

namespace Paper320

theorem three_pow_linear_lower (n : ℕ) : 2 * (n : ℝ) + 1 ≤ (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      push_cast
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

theorem finite_depth_error_fraction {d n : ℕ} (hn : n ≤ d) {ε : ℝ}
    (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    ε * ((3 / 2 : ℝ) * (3 ^ n - 1) - n) ≤
      (3 ^ (n + 1) - 3 - 2 * n) / 3 ^ (d + 1) ∧
      (3 ^ (n + 1) - 3 - 2 * (n : ℝ)) / 3 ^ (d + 1) < 1 := by
  have hD : (0 : ℝ) < 3 ^ (d + 1) := by positivity
  have hε : ε ≤ 2 / 3 ^ (d + 1) := (le_div_iff₀ hD).mpr hbudget
  have ha : 0 ≤ (3 / 2 : ℝ) * (3 ^ n - 1) - n := by
    nlinarith [three_pow_linear_lower n, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  constructor
  · calc
      _ ≤ (2 / 3 ^ (d + 1)) * ((3 / 2 : ℝ) * (3 ^ n - 1) - n) :=
        mul_le_mul_of_nonneg_right hε ha
      _ = _ := by rw [pow_succ (3 : ℝ) n]; ring
  · apply (div_lt_one hD).mpr
    have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

theorem comparisonV_step_bound {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    comparisonV ε L (n + 1) ≤ 2 * ε * L + 3 * ε * L * (3 ^ n - 1) ∧
      2 * ε * L + 3 * ε * L * (3 ^ n - 1) = ε * L * (3 ^ (n + 1) - 1) := by
  obtain ⟨hu, hv⟩ := comparison_bounds d ε L hε hL hbudget n hn
  constructor
  · rw [comparisonV_succ]
    nlinarith [mul_le_mul_of_nonneg_left hu hε]
  · rw [pow_succ]
    ring

end Paper320

end OAI
