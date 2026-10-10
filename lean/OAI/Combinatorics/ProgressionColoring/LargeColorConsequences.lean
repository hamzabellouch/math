import OAI.Combinatorics.ProgressionColoring.LargeColorGrowth
import OAI.Combinatorics.ProgressionColoring.GrowthConsequences

namespace OAI

/-!
# Unconditional growth in the number of colors

These conclusions use the actual digit norm coloring and proved finite upper
bound. They do not assume the uniform two-color construction used for growth
in the progression length.
-/

namespace QuantitativeVanDerWaerden

open Filter

/-- Uniform divergence over every integer progression length at least three. -/
theorem color_rate_tendsto :
    Tendsto (fun r : ℕ => ⨅ k : {k : ℕ // 3 ≤ k},
      Real.log (W r k.val : ℝ) / Real.log (r : ℝ)) atTop atTop := by
  exact uniform_color_rate_tendsto (F := fun r k => (W r k : ℝ)) (R := 256)
    (fun r hr k hk => LargeColor.exp_bound hr hk)

/-- For every fixed progression length at least three, the number grows
faster than every fixed real power of the number of colors. -/
theorem fixed_length_polynomial_ratio_tendsto {k : ℕ} (hk : 3 ≤ k) (A : ℝ) :
    Tendsto (fun r : ℕ => (W r k : ℝ) / (r : ℝ) ^ A) atTop atTop := by
  apply polynomial_ratio_tendsto_of_exp_sq_log
    (F := fun r => (W r k : ℝ)) (C := 64 * Real.log 2) (by positivity) A
  filter_upwards [eventually_ge_atTop (256 : ℕ)] with r hr
  exact LargeColor.exp_bound hr hk

end QuantitativeVanDerWaerden

end OAI
