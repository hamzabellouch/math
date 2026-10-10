import OAI.Algebra.DepthFive.BetaRefinements
import OAI.Algebra.DepthFive.RunWeights

namespace OAI

/-! Concrete numerical hypotheses for the balanced path-word sum. -/
noncomputable section

namespace Problem335.LowerParameters

theorem one_le_inv_alpha {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ (alpha n)⁻¹ :=
  (one_le_inv₀ (alpha_pos hn)).mpr (alpha_lt_one hn).le

/-- Every true run costs at most one factor of the matrix dimension. -/
theorem alpha_run_scale_le {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (-(1 + rho n)) ≤ (n : ℝ) :=
  RunWeights.scale_le_of_inv_le_sqrt (alpha_pos hn) (alpha_lt_one hn).le
    (rho_lt_one hn).le (Nat.cast_nonneg n) (inv_alpha_le_sqrt hn)

/-- The accumulated beta rounding error is already bounded by one half. -/
theorem word_error_mul_n_le_half {n : ℕ} (hn : 16 ≤ n) :
    (2 / (b n : ℝ)) * (n : ℝ) ≤ 1 / 2 := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos (by omega : 4 ≤ n)
  have hbn : 4 * (n : ℝ) ≤ (b n : ℝ) := by
    exact_mod_cast four_mul_n_le_b hn
  calc
    (2 / (b n : ℝ)) * (n : ℝ) = (2 * (n : ℝ)) / (b n : ℝ) := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith)

theorem word_error_mul_n_le_sqrt {n : ℕ} (hn : 16 ≤ n) :
    (2 / (b n : ℝ)) * (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_two (show 4 ≤ n by omega)
  exact (word_error_mul_n_le_half hn).trans (by linarith)

/-- All scalar premises of the corrected-word estimate, at the actual rounded
parameters. No word-product or graph hypothesis is part of this statement. -/
theorem word_weight_numeric_bounds {n : ℕ} (hn : 16 ≤ n) :
    0 < alpha n ∧ alpha n ≤ 1 ∧
    1 ≤ (alpha n)⁻¹ ∧ (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ) ∧
    0 ≤ beta n ∧
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (2 / (b n : ℝ)) ∧
    (alpha n) ^ (-(1 + rho n)) ≤ (n : ℝ) ∧
    0 ≤ 2 / (b n : ℝ) ∧
    (2 / (b n : ℝ)) * (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  exact ⟨alpha_pos hn4, (alpha_lt_one hn4).le, one_le_inv_alpha hn4,
    inv_alpha_le_sqrt hn4, (beta_pos hn4).le, beta_le_rpow_mul_exp_two_div hn,
    alpha_run_scale_le hn4, by positivity, word_error_mul_n_le_sqrt hn⟩

end Problem335.LowerParameters

end

end OAI
