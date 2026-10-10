import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
noncomputable section
namespace CuntzPureness

theorem geometric_shell_bound_summable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r ^ n * (3 * (n : ℝ) + 2) ^ 2) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  apply ((h2.mul_left (9 : ℝ)).add ((h1.mul_left (12 : ℝ)).add (h0.mul_left (4 : ℝ)))).congr
  intro n
  ring
end CuntzPureness

end

end OAI
