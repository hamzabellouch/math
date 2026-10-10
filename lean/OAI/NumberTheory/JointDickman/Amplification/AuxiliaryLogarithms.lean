import OAI.NumberTheory.JointDickman.Arithmetic.RegularPrimeSets

namespace OAI

/-! # Logarithmic scales for the regularity grid -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliaryLogLength_tendsto : Tendsto auxiliaryLogLength atTop atTop :=
  Real.tendsto_log_atTop.comp auxiliaryRatio_tendsto

theorem log_auxiliaryCutoff (B : ℕ) :
    Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
  simp [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]

theorem auxiliaryLogLength_eq {B : ℕ} (hB : 1 < B) :
    auxiliaryLogLength B = Real.log B - Real.log 1000 - Real.log (Real.log B) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength, auxiliaryRatio, Real.log_div hB0.ne' (mul_pos (by norm_num) hlog).ne',
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hlog.ne']
  ring

theorem logLogCutoff_div_log_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / Real.log B) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hconst : Tendsto (fun B : ℕ => Real.log 1000 / Real.log B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have h := hconst.add hsmall
  norm_num only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [log_auxiliaryCutoff, Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne', add_div]
  rfl

theorem auxiliaryLogLength_div_log_tendsto :
    Tendsto (fun B : ℕ => auxiliaryLogLength B / Real.log B) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub logLogCutoff_div_log_tendsto_zero
  norm_num only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength_eq hB, log_auxiliaryCutoff,
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne']
  field_simp
  ring

theorem log_div_auxiliaryLogLength_tendsto :
    Tendsto (fun B : ℕ => Real.log B / auxiliaryLogLength B) atTop (𝓝 1) := by
  have h := auxiliaryLogLength_div_log_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using h

theorem logLogCutoff_div_auxiliaryLogLength_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / auxiliaryLogLength B) atTop (𝓝 0) := by
  have h := logLogCutoff_div_log_tendsto_zero.mul log_div_auxiliaryLogLength_tendsto
  norm_num only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : Real.log B ≠ 0 := (Real.log_pos (by exact_mod_cast hB)).ne'
  field_simp

end JointDickman

end OAI
