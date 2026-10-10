import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def compactnessWeight {d : ℕ} (n : ℕ) (x : Ambient d) : ℝ :=
  ((1 + ‖x‖) ^ (n + 1))⁻¹

theorem compactnessWeight_pos {d : ℕ} (n : ℕ) (x : Ambient d) : 0 < compactnessWeight n x := by
  dsimp only [compactnessWeight]
  positivity

theorem compactnessWeight_continuous {d : ℕ} (n : ℕ) :
    Continuous (compactnessWeight n : Ambient d → ℝ) :=
  ((continuous_const.add continuous_norm).pow (n + 1)).inv₀ (fun x => by
    change (1 + ‖x‖) ^ (n + 1) ≠ 0
    positivity)

theorem compactnessWeight_le_one {d : ℕ} (n : ℕ) (x : Ambient d) : compactnessWeight n x ≤ 1 := by
  have hp : (1 : ℝ) ≤ (1 + ‖x‖) ^ (n + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
  simpa only [compactnessWeight, one_div, inv_one] using!
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp

theorem compactnessWeight_le_inverseDistance {d : ℕ} (n : ℕ) (x : Ambient d) (hx : x ≠ 0) :
    compactnessWeight n x ≤ inverseDistancePow (n + 1) (0 : Ambient d) x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simpa only [compactnessWeight, inverseDistancePow, dist_zero_left, one_div] using!
    one_div_le_one_div_of_le (pow_pos hn (n + 1))
      (pow_le_pow_left₀ hn.le (by linarith : ‖x‖ ≤ 1 + ‖x‖) (n + 1))

theorem compactnessWeight_inv_bound {d : ℕ} (n : ℕ) (R : ℝ)
    (x : Ambient d) (hx : ‖x‖ ≤ R) : (compactnessWeight n x)⁻¹ ≤ (1 + R) ^ (n + 1) := by
  rw [compactnessWeight, inv_inv]
  exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hx) (n + 1)

end

end RieszRectifiability

end OAI
