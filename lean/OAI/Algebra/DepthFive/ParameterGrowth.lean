import OAI.Algebra.DepthFive.OccupationParameterBounds
import OAI.Algebra.DepthFive.ParameterBounds

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

/-- The actual multiplication order, without an extra conditional parameter hypothesis,
has the growth asserted in the rank-method parameter lemma. -/
theorem b_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (b n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by
  apply b_isTheta_of_eventually_beta_bound
  obtain ⟨N, hN⟩ := eventually_q_beta_le_two_div_sqrt
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact (hN n hn).2

/-- Simultaneous explicit growth bounds for the two rounded orders. -/
theorem eventually_order_growth_bounds :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 4 ≤ (a n : ℝ) ∧
      (a n : ℝ) ≤ 3 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ∧
      (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 4 ≤ (b n : ℝ) ∧
      (b n : ℝ) ≤ 4 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_q_beta_le_two_div_sqrt
  refine ⟨max N 16, fun n hn => ?_⟩
  have hn16 : 16 ≤ n := (le_max_right _ _).trans hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  exact ⟨a_scale_lower hn16, a_scale_upper hn16, b_scale_lower hn16,
    b_scale_upper_of_beta_bound hn16 (hN n hnN).2⟩

end Problem335.LowerParameters

end

end OAI
