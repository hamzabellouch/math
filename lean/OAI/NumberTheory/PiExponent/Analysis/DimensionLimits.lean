import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

open Filter Topology

namespace PiExponent

 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

end PiExponent

end OAI
