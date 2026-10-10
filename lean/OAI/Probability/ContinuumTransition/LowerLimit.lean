import OAI.Probability.ContinuumTransition.PackingPressure

namespace OAI

section
open scoped Topology
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma cluster_ball_volume (t : ℝ) :
    volume.real (Metric.closedBall (0 : Space) (clusterRadius t)) =
      ((shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1))*Real.exp (-3*t) := by
  rw [Measure.addHaar_real_closedBall volume _ (clusterRadius_pos t).le]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd]
  unfold clusterRadius
  rw [mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℝ)*(-t) = -3*t by ring]
  ring

lemma cluster_ball_constant_pos : 0 < (shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1) := by
  apply mul_pos (by unfold shellDelta; positivity)
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

lemma tetra_log_scaled_tendsto {η : ℝ} (hη : 0 < η) (h : ℝ) :
    Tendsto (fun t : ℝ =>
      Real.log (volume.real (Metric.closedBall (0 : Space) (η/8))*
        (volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*Real.exp (4*(t*h))/24)/t)
      atTop (𝓝 (4*h-9)) := by
  let C := (shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1)
  let V := volume.real (Metric.closedBall (0 : Space) (η/8))
  have hC : 0 < C := cluster_ball_constant_pos
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hi := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
    (Real.log V+3*Real.log C-Real.log 24)).const_add (4*h-9)
  simp only [mul_zero,add_zero] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [cluster_ball_volume]
  change 4*h-9+(Real.log V+3*Real.log C-Real.log 24)*t⁻¹ =
    Real.log (V*(C*Real.exp (-3*t))^3*Real.exp (4*(t*h))/24)/t
  rw [Real.log_div (mul_pos (mul_pos hV (pow_pos (mul_pos hC (Real.exp_pos _)) 3)) (Real.exp_pos _)).ne' (by norm_num),
    Real.log_mul (mul_pos hV (pow_pos (mul_pos hC (Real.exp_pos _)) 3)).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_mul hV.ne' (pow_ne_zero 3 (mul_pos hC (Real.exp_pos _)).ne'),
    Real.log_pow, Real.log_mul hC.ne' (Real.exp_pos _).ne',Real.log_exp]
  field_simp
  ring

lemma core_one_lower_eventually {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) {c : ℝ}
    (hc : c < (packingDensity/(1+η)^3)*h) :
    ∀ᶠ t : ℝ in atTop, c < physicalPressure (coreProfile t) t (β,h) := by
  have hi := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
    (Real.log (volume.real (Metric.closedBall (0 : Space) (η/4))))).const_add h).const_mul
    (packingDensity/(1+η)^3)
  simp only [mul_zero,add_zero] at hi
  filter_upwards [hi.eventually_const_lt hc,eventually_gt_atTop (1 : ℝ)] with t ht h1
  apply ht.trans_le
  simpa only [div_eq_mul_inv] using core_pressure_one_lower h1 hβ hη h

lemma core_tetra_lower_eventually {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) {c : ℝ}
    (hc : c < (packingDensity/(1+η)^3)*(4*h-9)) :
    ∀ᶠ t : ℝ in atTop, c < physicalPressure (coreProfile t) t (β,h) := by
  have hi := (tetra_log_scaled_tendsto hη h).const_mul (packingDensity/(1+η)^3)
  have hfit : ∀ᶠ t : ℝ in atTop, 2*Real.exp (-t) < η/8 := by
    have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
    simp only [mul_zero] at hh
    exact hh.eventually_lt_const (by positivity)
  filter_upwards [hi.eventually_const_lt hc,eventually_gt_atTop (1 : ℝ),hfit] with t ht h1 hf
  exact ht.trans_le (core_pressure_tetra_lower h1 hβ hη hf.le h)

lemma packing_dilate_tendsto (a : ℝ) :
    Tendsto (fun η : ℝ => (packingDensity/(1+η)^3)*a) (𝓝[>] 0) (𝓝 (packingDensity*a)) := by
  have hh : Tendsto (fun η : ℝ => (packingDensity/(1+η)^3)*a) (𝓝 0)
      (𝓝 ((packingDensity/(1+(0 : ℝ))^3)*a)) :=
    (tendsto_const_nhds.div ((tendsto_id.const_add 1).pow 3) (by norm_num)).mul_const a
  simpa only [add_zero,one_pow,div_one] using hh.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

lemma exists_packing_dilate_lt {c a : ℝ} (hc : c < packingDensity*a) :
    ∃ η : ℝ, 0 < η ∧ c < (packingDensity/(1+η)^3)*a := by
  have hh := (packing_dilate_tendsto a).eventually_const_lt hc
  obtain ⟨η,hη,he⟩ := (hh.and self_mem_nhdsWithin).exists
  exact ⟨η,he,hη⟩

end ContinuumTemperature
end

end OAI
