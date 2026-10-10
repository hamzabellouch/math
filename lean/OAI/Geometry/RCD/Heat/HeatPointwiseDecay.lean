import OAI.Geometry.RCD.Heat.HeatMassSmoothing
import OAI.Geometry.RCD.Heat.HeatPointEvaluation
import OAI.Geometry.RCD.Heat.HeatInwardDecay

namespace OAI

/-! # Pointwise off-diagonal heat evaluation from cylinder mass -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem boundedHeat_offDiagonal_evaluation :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : X) (r t D : ℝ) (ht : 0 < t),
      0 < r → -1 ≤ K*r^2 → r^2 < t → r ≤ D →
      ∀ (f : Lp ℝ 2 (hausdorff n X)) (hf : HasBoundedAmplitude f),
      (∀ᵐ y ∂hausdorff n X, f y ≠ 0 → D ≤ dist x y) →
      |hX.boundedHeat hn p f hf t ht x| ≤
        C/Real.sqrt ((hausdorff n X).real (ball x r))*
          (Real.exp (-(D-r)^2/(4*t))*‖f‖) := by
  obtain ⟨C,hC,hbound⟩ := hX.heat_cylinder_L2_smoothing hn
  refine ⟨C,hC,?_⟩
  intro x r t D ht hr hcurv hrt hrD f hf hfar
  let μ := hausdorff n X
  let E := Real.exp (-(D-r)^2/(4*t))
  by_cases hfzero : f = 0
  · have h0 : ∀ᵐ y ∂μ, |f y| ≤ (0:ℝ≥0) := by
      subst f
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with y hy
      simp only [hy,Pi.zero_apply,abs_zero,NNReal.coe_zero,le_refl]
    have hh := hX.boundedHeat_abs_le hn p f hf t ht 0 h0 x
    simpa only [hfzero,norm_zero,mul_zero,NNReal.coe_zero] using hh
  have hM : 0 < E*‖f‖ := mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hfzero)
  have hmass : (∫ s in (t-r^2)..t, ∫ y in ball x r, (heatAt μ hX.quadratic s f y)^2 ∂μ) ≤
      r^2*(E*‖f‖)^2 := by
    have hc := continuous_setIntegral_sq_path μ (heatAt_continuous μ hX.quadratic f)
      (S := ball x r) measurableSet_ball
    have hpoint (s : ℝ) (hs : s ∈ Icc (t-r^2) t) :
        (∫ y in ball x r, (heatAt μ hX.quadratic s f y)^2 ∂μ) ≤ E^2*‖f‖^2 := by
      have hspos : 0 < s := lt_of_lt_of_le (sub_pos.mpr hrt) hs.1
      have hdec := heatAt_inward_L2_tail μ hX.quadratic f x hfar hrD hspos
        measurableSet_ball (fun y hy => by rw [dist_comm]; exact (mem_ball.mp hy).le)
      have hd : (D-r)^2/(2*t) ≤ (D-r)^2/(2*s) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith only [hs.2])
      have hexp : Real.exp (-(D-r)^2/(2*s)) ≤ E^2 := by
        have he : E^2 = Real.exp (-(D-r)^2/(2*t)) := by
          dsimp only [E]
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
          ring
        rw [he]
        apply Real.exp_le_exp.mpr
        simpa only [neg_div] using neg_le_neg hd
      exact hdec.trans (mul_le_mul_of_nonneg_right hexp (sq_nonneg _))
    have hh := intervalIntegral.integral_mono_on (by linarith [sq_nonneg r] : t-r^2 ≤ t)
      (hc.intervalIntegrable (μ := volume) _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => E^2*‖f‖^2) volume (t-r^2) t)
      (fun s hs => hpoint s hs)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_sub_cancel,mul_pow,mul_assoc] using hh
  have he : t-r^2+r^2 = t := by ring
  have ha := hbound x r (t-r^2) (E*‖f‖) hr hcurv (sub_pos.mpr hrt) hM f
  rw [he] at ha
  have hae := ha hmass
  let := hX.openPos K n
  have hmin : (fun y => min |hX.boundedHeat hn p f hf t ht y|
      (C/Real.sqrt (μ.real (ball x r))*(E*‖f‖))) =ᵐ[μ.restrict (ball x (r/2))]
      (fun y => |hX.boundedHeat hn p f hf t ht y|) := by
    filter_upwards [hae,ae_restrict_of_ae (hX.boundedHeat_represents hn p f hf t ht)] with y hy heq
    exact min_eq_left (by simpa only [heq] using hy)
  have hc := (hX.boundedHeat_continuous hn p f hf t ht).abs
  have heq := Measure.eqOn_open_of_ae_eq hmin isOpen_ball
    (hc.min continuous_const).continuousOn hc.continuousOn
  exact min_eq_left_iff.mp (heq (mem_ball_self (half_pos hr)))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
