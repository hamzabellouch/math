import OAI.Probability.ContinuumTransition.PackingLower

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma packing_ratio_affine_tendsto {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun L : ℝ => (packingNumber L : ℝ)/(a*L+b)^3) atTop (𝓝 (packingDensity/a^3)) := by
  have hf := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul b).const_add a).pow 3
  simp only [mul_zero,add_zero] at hf
  apply (packingNumber_tendsto.div hf (pow_ne_zero 3 ha.ne')).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have he : (a+b*L⁻¹) = (a*L+b)/L := by field_simp
  dsimp only [Pi.div_apply]
  rw [he,div_pow,div_div_div_cancel_right₀ (pow_ne_zero 3 hL.ne')]

theorem core_pressure_packing_lower {t β η r B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hη : 0 ≤ η) (hr : 2*r ≤ η) (hB : 0 < B) (h : ℝ) (n : ℕ)
    (hterm : ∀ c : Space, B ≤ familyTerm
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β (t*h)) (Metric.closedBall c r) n) :
    (packingDensity/(1+η)^3)*(Real.log B/t) ≤ physicalPressure (coreProfile t) t (β,h) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ha : 0 < 1+η := by linarith
  have hL : Tendsto (fun L : ℝ => (1+η)*L+2*r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((b-2*r)/(1+η))] with L hL
    have hh := (div_le_iff₀ ha).mp hL
    nlinarith
  have hright := (physicalPressure_tendsto
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _) (h := h)).comp hL
  have hleft := (packing_ratio_affine_tendsto ha (2*r)).mul_const (Real.log B/t)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ))] with L hpositive
  have hh := core_grand_packing_lower ht hβ hη hr hB.le (t*h) L n hterm
  have hlog := Real.log_le_log (pow_pos hB _) hh
  rw [Real.log_pow,grandIntegral_radial] at hlog
  have hd := div_le_div_of_nonneg_right hlog (show 0 ≤ t*((1+η)*L+2*r)^3 by positivity)
  convert hd using 1
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rfl

lemma core_pressure_one_lower {t β η : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) :
    (packingDensity/(1+η)^3)*(h+Real.log (volume.real (Metric.closedBall (0 : Space) (η/4)))/t) ≤
      physicalPressure (coreProfile t) t (β,h) := by
  have hv : 0 < volume.real (Metric.closedBall (0 : Space) (η/4)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hh := core_pressure_packing_lower ht hβ hη.le (r := η/4) (by linarith)
    (mul_pos hv (Real.exp_pos (t*h))) h 1 (fun c => (core_one_term t β (t*h) (η/4) c).ge)
  rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  convert hh using 1
  congr 1
  field_simp
  ring

lemma core_pressure_tetra_lower {t β η : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (hη : 0 < η)
    (hfit : 2*Real.exp (-t) ≤ η/8) (h : ℝ) :
    (packingDensity/(1+η)^3)*
      (Real.log (volume.real (Metric.closedBall (0 : Space) (η/8))*
        (volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*Real.exp (4*(t*h))/24)/t) ≤
      physicalPressure (coreProfile t) t (β,h) := by
  have hv : 0 < volume.real (Metric.closedBall (0 : Space) (η/8)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hw : 0 < volume.real (Metric.closedBall (0 : Space) (clusterRadius t)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (clusterRadius_pos t)).ne' measure_closedBall_lt_top.ne
  apply core_pressure_packing_lower ht hβ hη.le (r := η/4) (by linarith)
    (by positivity) h 4
  intro c
  have hh := tetraTrial_term_lower (r := η/4) ht hβ (by simpa only [div_div,show (4:ℝ)*2=8 by norm_num] using hfit) (t*h) c
  simpa only [Measure.real, Measure.addHaar_closedBall_center,div_div,show (4:ℝ)*2=8 by norm_num] using hh

end ContinuumTemperature
end

end OAI
