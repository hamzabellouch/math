import OAI.Analysis.KadisonKastler.FiniteBlockPartition
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Normalized sizes of equal matrix blocks -/

namespace KadisonKastler

open Filter
open scoped Topology

theorem tendsto_finiteBlock_ratio (k : ℕ) (hk : 0 < k) :
    Tendsto (fun j : ℕ => (((j + 1) / k : ℕ) : ℝ) / (j + 1 : ℝ)) atTop
      (𝓝 (1 / (k : ℝ))) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hbounds (j : ℕ) :
      1 / (k : ℝ) - 1 / (j + 1 : ℝ) ≤ (((j + 1) / k : ℕ) : ℝ) / (j + 1 : ℝ) ∧
      (((j + 1) / k : ℕ) : ℝ) / (j + 1 : ℝ) ≤ 1 / (k : ℝ) := by
    have hj : (0 : ℝ) < j + 1 := by positivity
    have hdiv : (((j + 1) % k : ℕ) : ℝ) + (k : ℝ) * (((j + 1) / k : ℕ) : ℝ) = j + 1 := by
      exact_mod_cast Nat.mod_add_div (j + 1) k
    have hrem : (((j + 1) % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt (j + 1) hk
    have hrem0 : (0 : ℝ) ≤ ((j + 1) % k : ℕ) := by positivity
    constructor
    · calc
        1 / (k : ℝ) - 1 / (j + 1 : ℝ) =
            ((j + 1 : ℝ) - k) / ((j + 1 : ℝ) * k) := by
              field_simp [ne_of_gt hj, ne_of_gt hkr]
        _ ≤ ((k : ℝ) * (((j + 1) / k : ℕ) : ℝ)) / ((j + 1 : ℝ) * k) :=
          div_le_div_of_nonneg_right (by linarith) (mul_nonneg hj.le hkr.le)
        _ = (((j + 1) / k : ℕ) : ℝ) / (j + 1 : ℝ) := by
          field_simp [ne_of_gt hj, ne_of_gt hkr]
    · apply (div_le_div_iff₀ hj hkr).mpr
      nlinarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun j : ℕ => 1 / (k : ℝ) - 1 / (j + 1 : ℝ)) atTop (𝓝 (1 / (k : ℝ))) from by
      have hc : Tendsto (fun _ : ℕ => 1 / (k : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := tendsto_const_nhds
      simpa only [sub_zero] using hc.sub tendsto_one_div_add_atTop_nhds_zero_nat)
    tendsto_const_nhds (fun j => (hbounds j).1) (fun j => (hbounds j).2)

end KadisonKastler

end OAI
