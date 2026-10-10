import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # The elementary logarithmic losses used in the minor-arc specialization -/
namespace JointDickman
open Filter
open scoped Topology

theorem eventually_nat_log_linear (A : ℝ) :
    ∀ᶠ B : ℕ in atTop, A*Real.log B ≤ (B:ℝ) := by
  have hlim : Tendsto (fun B : ℕ => A*Real.log B/(B:ℝ)) atTop (𝓝 0) := by
    have h := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ) < 1)).const_mul A).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_div_assoc] using h
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  have hB0 : (0:ℝ) < B := by exact_mod_cast hB
  exact (div_le_one hB0).mp hsmall

theorem eventually_nat_one_add_log_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, 1+Real.log B ≤ 2*(B:ℝ)^δ := by
  have hlim : Tendsto (fun B : ℕ => Real.log B/(B:ℝ)^δ) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (log_power_div_power_tendsto_zero 1 hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hp : 0 < (B:ℝ)^δ := Real.rpow_pos_of_pos (by linarith) δ
  have hl : Real.log B ≤ (B:ℝ)^δ := (div_le_one hp).mp hsmall
  have h1 : 1 ≤ (B:ℝ)^δ := Real.one_le_rpow hB1 hδ.le
  linarith

end JointDickman

end OAI
