import OAI.Analysis.LipschitzHilbert.Estimates.FiniteLogAmplitudeSum
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! The support-measure class is chosen from the actual positive
measure by the integer floor of its base-two logarithm. -/
noncomputable section
namespace LipschitzHilbert

def dyadicMeasureClass (m : ℝ) : ℤ := ⌊Real.log m/Real.log 2⌋

theorem dyadicMeasureClass_bounds {m : ℝ} (hm : 0<m) :
    (2:ℝ)^(dyadicMeasureClass m)≤m ∧ m<(2:ℝ)^(dyadicMeasureClass m+1) := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (Real.log_le_log_iff (zpow_pos (by norm_num) _) hm).mp
    rw [Real.log_zpow]
    exact (le_div_iff₀ hc).mp (Int.floor_le _)
  · apply (Real.log_lt_log_iff hm (zpow_pos (by norm_num) _)).mp
    rw [Real.log_zpow,Int.cast_add,Int.cast_one]
    exact (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)

end LipschitzHilbert

end

end OAI
