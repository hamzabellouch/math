import OAI.NumberTheory.JointDickman.Amplification.AmplificationMultiplier

namespace OAI

/-! # The model's inverse-length row moment is smaller than the sampling scale -/
namespace JointDickman
open Filter
open scoped Topology

theorem amplification_inverse_square_rate (C : ℝ) :
    ∀ᶠ B : ℕ in atTop, C/(amplificationMultiplier B : ℝ) ≤ (B : ℝ)^(-(21/100 : ℝ)) := by
  have ht := (power_div_amplificationMultiplier (by norm_num : (21/100 : ℝ) < 8/25)).const_mul C
  have ht' : Tendsto (fun B : ℕ => C*((B : ℝ)^(21/100 : ℝ)/amplificationMultiplier B))
      atTop (𝓝 0) := by simpa only [mul_zero] using ht
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hb hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hp : 0 < (B : ℝ)^(21/100 : ℝ) := Real.rpow_pos_of_pos hBp _
  rw [Real.rpow_neg hBp.le,← one_div]
  apply (le_div_iff₀ hp).mpr
  calc
    _ = C*((B : ℝ)^(21/100 : ℝ)/amplificationMultiplier B) := by ring
    _ ≤ 1 := hb

end JointDickman

end OAI
