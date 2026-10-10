import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

/-! # The logarithmic growth rate needed for the finite-zero contradiction -/

namespace Ostmann

open Filter
open scoped Topology

theorem logarithmic_disk_rate (A b D : ℝ) (hb : 1 ≤ b) :
    Tendsto (fun n : ℕ =>
      (A * ((n : ℝ) + b) * (1 + Real.log ((n : ℝ) + b)) + D) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => (b - 1) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hy
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + b) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have hh := hc.const_add 1
    convert hh using 1
    · funext n
      field_simp
      ring
    · simp
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + b) / ((n : ℝ) + b)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  have hlog' : Tendsto (fun n : ℕ => (1 + Real.log ((n : ℝ) + b)) / ((n : ℝ) + b)) atTop (𝓝 0) := by
    simpa only [zero_add, add_div] using (tendsto_const_nhds.div_atTop hx).add hlog
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hy
  have hd : Tendsto (fun n : ℕ => D / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hh := ((hr.pow 2).const_mul A).mul hlog' |>.add hd
  simp only [one_pow, mul_one, mul_zero, zero_add] at hh
  convert hh using 1
  funext n
  have hxn : (n : ℝ) + b ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hyn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hxn, hyn]

end Ostmann

end OAI
