import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace Yau.Analysis
open Filter
open scoped Topology
noncomputable section

theorem hasSum_scaled_geometric_shift (r : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ ↦ r*(1/2:ℝ)^(n+m)) (r*(1/2:ℝ)^m*2) := by
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using
    hasSum_geometric_two.mul_left (r*(1/2:ℝ)^m)

theorem tsum_scaled_geometric_two (r : ℝ) :
    (∑' n : ℕ, r*(1/2:ℝ)^(n+2)) = r/2 := by
  convert (hasSum_scaled_geometric_shift r 2).tsum_eq using 1
  ring

theorem tsum_scaled_geometric_three (r : ℝ) :
    (∑' n : ℕ, r*(1/2:ℝ)^(n+3)) = r/4 := by
  convert (hasSum_scaled_geometric_shift r 3).tsum_eq using 1
  ring

end
end Yau.Analysis

end OAI
