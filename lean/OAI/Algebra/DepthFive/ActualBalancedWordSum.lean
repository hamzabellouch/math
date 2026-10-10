import OAI.Algebra.DepthFive.BalancedWordSum
import OAI.Algebra.DepthFive.WordWeightParameters

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- The complete corrected path-word estimate at the actual lower-bound
parameters and balanced schedule. There are no remaining weight assumptions. -/
theorem actual_balanced_word_sum_bound {n : ℕ} (hn : 16 ≤ n) :
    (∑ w : Fin n → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges n)
        (Finset.univ.filter (fun i => balancedLayer (show 4 ≤ n by omega) i = true))
        BalancedSchedule.adjacent (alpha n)⁻¹ (beta n) ((n : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt (n : ℝ)) := by
  have hn4 : 4 ≤ n := by omega
  exact balanced_word_sum_bound hn4 (alpha_pos hn4) (alpha_lt_one hn4).le
    (inv_alpha_le_sqrt hn4) (beta_pos hn4).le (beta_le_rpow_mul_exp_two_div hn)
    (alpha_run_scale_le hn4) (by positivity) (word_error_mul_n_le_sqrt hn)

end Problem335.LowerParameters

end

end OAI
