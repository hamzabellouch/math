import OAI.NumberTheory.SiegelZeros.EntireFunctions.AffineCircles

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W01

open Filter Asymptotics
open scoped Topology

theorem tendsto_add_div_self (a : ℝ) :
    Tendsto (fun x : ℝ => (a + x) / x) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero.const_mul a).add_const 1
  have he : (fun x : ℝ => a * x⁻¹ + 1) =ᶠ[atTop] (fun x => (a + x) / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  exact Filter.Tendsto.congr' he (by simpa only [mul_zero, zero_add] using h)

theorem tendsto_logSquare_profile_div_sq :
    Tendsto (fun R : ℝ => (1 + R) * (Real.log (2 + R)) ^ 2 / R ^ 2)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := (1 : ℝ)) zero_lt_one).tendsto_div_nhds_zero
  have hlog' := hlog.comp (tendsto_atTop_add_const_left atTop (2 : ℝ) tendsto_id)
  have h := ((tendsto_add_div_self 1).mul (tendsto_add_div_self 2)).mul hlog'
  have he : (fun R : ℝ => ((1 + R) / R * ((2 + R) / R)) *
      ((Real.log (2 + R)) ^ 2 / (2 + R))) =ᶠ[atTop]
      (fun R : ℝ => (1 + R) * (Real.log (2 + R)) ^ 2 / R ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hR2 : 2 + R ≠ 0 := by linarith
    field_simp [hR.ne', hR2]
  exact Filter.Tendsto.congr' he (by
    simpa only [one_mul, mul_zero, Function.comp_apply, id_eq] using h)

theorem doubled_radius_growth_le_logSquare {R r : ℝ} (hR : 0 ≤ R)
    (hr : 0 ≤ r) (hrR : r ≤ 2 * R) :
    (1 + r) * Real.log (2 + r) ≤ 12 * ((1 + R) * (Real.log (2 + R)) ^ 2) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogtwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlower : (1 / 2 : ℝ) ≤ Real.log (2 + R) :=
    htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hl : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + r) ≤ 3 * Real.log (2 + R) := by
    have hh : Real.log (2 + r) ≤ Real.log 2 + Real.log (2 + R) := by
      calc
        _ ≤ Real.log (2 * (2 + R)) := Real.log_le_log (by positivity) (by linarith)
        _ = _ := Real.log_mul (by norm_num) (by positivity)
    linarith
  have hm := mul_le_mul (show 1 + r ≤ 2 * (1 + R) by linarith) hlog hl (by positivity)
  have hsq : Real.log (2 + R) ≤ 2 * (Real.log (2 + R)) ^ 2 := by nlinarith
  have hm' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * (1 + R) by positivity)
  nlinarith

end SiegelZerosAwei.Workers.W01

end

end SiegelZeros

end OAI
