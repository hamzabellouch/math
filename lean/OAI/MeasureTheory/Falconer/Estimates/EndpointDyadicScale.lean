import OAI.MeasureTheory.Falconer.Estimates.EndpointPowerAbsorption

namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

theorem dyadic_depth_of_inverse_lt {N B : ℕ}
    (h : 1/(2:ℝ)^N < 1/(2:ℝ)^B) : B ≤ N := by
  by_contra hn
  have hp : (2:ℝ)^N ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : 1/(2:ℝ)^B ≤ 1/(2:ℝ)^N := one_div_le_one_div_of_le (by positivity) hp
  exact (not_lt_of_ge hi) h

theorem dyadic_inverse_rpow (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^(-c) = (1/(2:ℝ)^N)^c := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem dyadic_loss_conversion (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^c = (1/(2:ℝ)^N)^(-c) := by
  simpa only [neg_neg] using dyadic_inverse_rpow N (-c)

end Falconer

end OAI
