import OAI.Geometry.RCD.Heat.HeatDensityTails
import OAI.Geometry.RCD.Metric.BoundedRegionVolume

namespace OAI

/-! # Uniform L² tightness of nearby heat-density rows -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

theorem gaussian_shift_tendsto_zero (r t Q : ℝ) (ht : 0 < t) :
    Tendsto (fun D : ℝ => Q*Real.exp (-(D-r)^2/(2*t))) atTop (𝓝 0) := by
  have hs : Tendsto (fun D : ℝ => D-r) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-r) tendsto_id
  have hp := (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp hs
  have hd := hp.atTop_div_const (by positivity : 0 < 2*t)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hd
  simpa only [Function.comp_def,neg_div,mul_zero] using he.const_mul Q

namespace NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonDensity_uniform_L2_tail (t : ℝ) (ht : 0 < t) (x₀ : X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x ∈ ball x₀ 1,
      (∫ y in (closedBall x₀ L)ᶜ, (hX.heatRadonDensity hn p t ht x y)^2 ∂hausdorff n X) ≤ ε := by
  obtain ⟨r,C,hr,hC,htail⟩ := hX.heatRadonDensity_L2_tail hn p t ht
  obtain ⟨m,hm,hvol⟩ := hX.ball_volume_lower_on_bounded_region hn x₀ 1 r hr
  let q := C/Real.sqrt m
  have hq : 0 ≤ q := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hlim := gaussian_shift_tendsto_zero r t (q^2) ht
  obtain ⟨D,hDr,hD⟩ := ((eventually_ge_atTop r).and (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨D+1,by linarith,?_⟩
  intro x hx
  have hv := hvol x (mem_ball.mp hx).le
  have hfrac : C/Real.sqrt ((hausdorff n X).real (ball x r)) ≤ q :=
    div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt hv)
  have hsub : (closedBall x₀ (D+1))ᶜ ⊆ {y | D ≤ dist x y} := by
    intro y hy
    have hy' : D+1 < dist y x₀ := lt_of_not_ge (fun hh => hy (mem_closedBall.mpr hh))
    have hd := dist_triangle y x x₀
    rw [dist_comm y x] at hd
    have hx' := mem_ball.mp hx
    change D ≤ dist x y
    linarith
  have hs := setIntegral_mono_set (hX.heatRadonDensity_memLp_two hn p t ht x).integrable_sq.integrableOn
    (Eventually.of_forall fun y => sq_nonneg (hX.heatRadonDensity hn p t ht x y))
    (Eventually.of_forall hsub)
  have hb := hs.trans (htail x D hDr)
  have hcoef : (C/Real.sqrt ((hausdorff n X).real (ball x r))*Real.exp (-(D-r)^2/(4*t)))^2 ≤
      q^2*Real.exp (-(D-r)^2/(2*t)) := by
    have he : Real.exp (-(D-r)^2/(4*t))^2 = Real.exp (-(D-r)^2/(2*t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
      ring
    rw [mul_pow,he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfrac 2) (Real.exp_pos _).le
  exact (hb.trans hcoef).trans hD.le

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
