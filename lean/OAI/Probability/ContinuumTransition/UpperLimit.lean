import OAI.Probability.ContinuumTransition.PackingUpper

namespace OAI

section
open scoped Topology
open Filter
namespace ContinuumTemperature

noncomputable def idealCorePressure (h : ℝ) : ℝ := max 0 (max (packingDensity*h) (4*packingDensity*h-9*packingDensity))

lemma idealCorePressure_eq (h : ℝ) :
    packingDensity*max 0 (h+3*max 0 (h-3)) = idealCorePressure h := by
  unfold idealCorePressure
  have hp := packingDensity_pos
  by_cases h3 : 3 ≤ h
  · rw [max_eq_right (sub_nonneg.mpr h3)]
    rw [max_eq_right (by linarith : 0 ≤ h+3*(h-3))]
    rw [max_eq_right (by nlinarith : packingDensity*h ≤ 4*packingDensity*h-9*packingDensity)]
    rw [max_eq_right (by nlinarith : 0 ≤ 4*packingDensity*h-9*packingDensity)]
    ring
  · have h3' : h ≤ 3 := (lt_of_not_ge h3).le
    rw [max_eq_left (sub_nonpos.mpr h3'), mul_zero,add_zero]
    rw [max_eq_left (by nlinarith : 4*packingDensity*h-9*packingDensity ≤ packingDensity*h)]
    simpa only [mul_zero] using mul_max_of_nonneg (0 : ℝ) h hp.le

lemma bad_activity_div_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (t*h-β*t^2/2)/t) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => 1/t) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  apply squeeze_zero' _ _ hi
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (max 1 (2*h/β))] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht)
    have hh : 2*h ≤ β*t := by
      have hh := (div_le_iff₀ hβ).mp ((le_max_right _ _).trans ht)
      nlinarith
    have hex : t*h-β*t^2/2 ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]
    apply div_le_div_of_nonneg_right _ ht0.le
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hex

lemma log_clusterActivity_scaled_tendsto (h : ℝ) :
    Tendsto (fun t : ℝ => Real.log (max 1 (clusterActivity t (t*h)))/t)
      atTop (𝓝 (max 0 (h+3*max 0 (h-3)))) := by
  have hi : Tendsto (fun t : ℝ => Real.log shellVolumeConstant/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log shellVolumeConstant)
  have hh := (tendsto_const_nhds (x := (0 : ℝ))).max (((tendsto_const_nhds (x := h)).add
    (((tendsto_const_nhds (x := (0 : ℝ))).max
      ((hi.sub_const 3).add_const h)).const_mul 3)))
  have heq : max (0 : ℝ) (h+3*max 0 (0-3+h)) = max 0 (h+3*max 0 (h-3)) := by ring_nf
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [log_clusterActivity]
  have he : max 0 (t*h+3*max 0 (Real.log shellVolumeConstant-3*t+t*h))/t =
      max 0 (h+3*max 0 (Real.log shellVolumeConstant/t-3+h)) := by
    rw [← max_div_div_right ht.le,zero_div,add_div,
      mul_div_assoc 3, ← max_div_div_right ht.le,zero_div,add_div,sub_div]
    field_simp
  simpa only [sub_zero,zero_sub,zero_add] using he.symm

lemma core_upper_bound_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ =>
      (1+Real.exp (t*h-β*t^2/2)+packingDensity*(2+Real.log (max 1 (clusterActivity t (t*h)))))/t)
      atTop (𝓝 (idealCorePressure h)) := by
  have hi : Tendsto (fun t : ℝ => 1/t) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hh := (hi.add (bad_activity_div_tendsto hβ h)).add
    (((hi.const_mul 2).add (log_clusterActivity_scaled_tendsto h)).const_mul packingDensity)
  simp only [mul_zero,zero_add,idealCorePressure_eq] at hh
  convert hh using 1
  funext t
  ring

end ContinuumTemperature
end

end OAI
