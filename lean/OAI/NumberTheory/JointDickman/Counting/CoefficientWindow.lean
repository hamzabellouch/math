import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # The coefficient expansion on a fixed scaled support -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_support_window {a : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9 / 10 : ℝ) * B ≤ Real.log X →
      9 ≤ a * X ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
  have hloglim : Tendsto (fun B : ℕ => Real.log a / B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hpowlim : Tendsto (fun B : ℕ => (B : ℝ) ^ (-(11 / 100 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp tendsto_natCast_atTop_atTop
  have hpowlarge : Tendsto (fun B : ℕ => (B : ℝ) ^ (89 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hloglim.eventually (Ioi_mem_nhds (by norm_num : -(9 / 20 : ℝ) < 0)),
    hpowlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 9 / 20)),
    hpowlarge.eventually_ge_atTop (Real.log 9), eventually_gt_atTop 0] with B hloga hsmall hlarge hB
  intro X hX hlogX
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlower : -(9 / 20 : ℝ) * B ≤ Real.log a := (lt_div_iff₀ hB0).mp hloga |>.le
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) = (B : ℝ) ^ (-(11 / 100 : ℝ)) * B := by
    calc
      _ = (B : ℝ) ^ (-(11 / 100 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hB0, Real.rpow_one]
  have hs : (B : ℝ) ^ (89 / 100 : ℝ) ≤ (9 / 20 : ℝ) * B := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_right hsmall.le hB0.le
  have hbound : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
    rw [Real.log_mul ha.ne' hX.ne']
    linarith
  exact ⟨(Real.log_le_log_iff (by norm_num) (mul_pos ha hX)).mp (hlarge.trans hbound), hbound⟩

end JointDickman

end OAI
