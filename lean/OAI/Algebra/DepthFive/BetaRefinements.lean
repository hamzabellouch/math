import OAI.Algebra.DepthFive.AnalyticParameters
import OAI.Algebra.DepthFive.FractionRounding

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

/-- The rounded multiplication fraction has logarithmic error at most `2/b`. -/
theorem beta_log_error_bounds {n : ℕ} (hn : 16 ≤ n) :
    0 ≤ Real.log (beta n / ((alpha n) ^ (rho n))) ∧
      Real.log (beta n / ((alpha n) ^ (rho n))) ≤ 2 / (b n : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn4
  have hp : 0 < (alpha n) ^ (rho n) := alpha_rpow_rho_pos hn4
  have hp1 : (alpha n) ^ (rho n) < 1 := alpha_rpow_rho_lt_one hn4
  have hpm : 0 < 1 - (alpha n) ^ (rho n) := sub_pos.mpr hp1
  have hx := b0_pos hn4
  have hab := a_le_b0 hn4
  have ha : 4 * (n : ℝ) ≤ (a n : ℝ) := by exact_mod_cast four_mul_n_le_a hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hxone : 1 ≤ b0 n := by linarith
  have hbase : b0 n / (b0 n + (u n : ℝ)) = (alpha n) ^ (rho n) := by
    unfold b0
    field_simp [ne_of_gt hu, ne_of_gt hpm]
    ring
  have hratio : ((b n : ℝ) / ((b n : ℝ) + (u n : ℝ))) /
      (b0 n / (b0 n + (u n : ℝ))) = beta n / ((alpha n) ^ (rho n)) := by
    rw [hbase, beta]
  constructor
  · rw [← hratio]
    exact (fraction_rounding_log_bounds hx hu (b0_le_b n) (b_lt_b0_add_one hn4).le).1
  · rw [← hratio]
    exact fraction_rounding_log_le_two_div hxone hu (b0_le_b n) (b_lt_b0_add_one hn4).le

/-- Sharp multiplicative rounding bound used when summing path runs. -/
theorem beta_le_rpow_mul_exp_two_div {n : ℕ} (hn : 16 ≤ n) :
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (2 / (b n : ℝ)) := by
  have hn4 : 4 ≤ n := by omega
  have hp : 0 < (alpha n) ^ (rho n) := alpha_rpow_rho_pos hn4
  have hratio : 0 < beta n / ((alpha n) ^ (rho n)) := div_pos (beta_pos hn4) hp
  have h := (Real.log_le_iff_le_exp hratio).mp (beta_log_error_bounds hn).2
  exact ((div_le_iff₀ hp).mp h).trans_eq (mul_comm _ _)

end Problem335.LowerParameters

end

end OAI
