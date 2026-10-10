import OAI.Geometry.CylinderCovering.Rational.EnergyIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.Coefficients

namespace OAI

open Set MeasureTheory Filter SlopeRational
open scoped Topology

noncomputable section

namespace RationalEnergy

private theorem vec2_zero (x y : ℝ) : vec2 x y 0 = x := rfl
private theorem vec2_one (x y : ℝ) : vec2 x y 1 = y := rfl

private theorem plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have hn : ‖z‖^2 = (z 0)^2+(z 1)^2 := by
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs]
  nlinarith [abs_nonneg (z 0), abs_nonneg (z 1), sq_abs (z 0), sq_abs (z 1)]

theorem baseDomain_mem_iff (z : Plane) : z ∈ baseDomain ↔
    z 1 ∈ Icc (0:ℝ) (1/2) ∧
      z 0 ∈ Icc (-(radius (z 1))/2) (radius (z 1)/2) := by
  simp only [baseDomain, wedge, mem_inter_iff, mem_ofPred_eq, mem_Icc, radius, neg_div]
  rw [← abs_le]
  constructor
  · rintro ⟨hw, ht⟩
    constructor
    · exact ⟨ht, by linarith [abs_nonneg (z 0)]⟩
    · linarith
  · rintro ⟨⟨ht, _⟩, hy⟩
    exact ⟨by linarith, ht⟩

theorem baseDomain_isCompact : IsCompact baseDomain := by
  have hc : IsClosed baseDomain := by
    unfold baseDomain wedge radius
    exact (isClosed_le (f := fun z : Plane => 2*|z 0|)
      (g := fun z => 1/2-z 1) (by fun_prop) (by fun_prop)).inter
      (isClosed_le (f := fun _ : Plane => (0:ℝ))
        (g := fun z => z 1) (by fun_prop) (by fun_prop))
  apply (isCompact_closedBall (0:Plane) 1).of_isClosed_subset hc
  intro z hz
  have hz' := (baseDomain_mem_iff z).1 hz
  have hy : |z 0| ≤ radius (z 1)/2 := abs_le.mpr ⟨by linarith [hz'.2.1], hz'.2.2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn := plane_norm_le_sum z
  rw [abs_of_nonneg hz'.1.1] at hn
  dsimp [radius] at hy
  linarith [hz'.1.2]

theorem energyDensity_continuousOn {d : ℝ} (hd : 0 < d) :
    ContinuousOn (energyDensity d) baseDomain := by
  intro z hz
  have hz' := (baseDomain_mem_iff z).1 hz
  have hden : 0 < (1/2-z 1)+d := by
    linarith [hz'.1.2]
  apply ContinuousAt.continuousWithinAt
  unfold energyDensity a b radius
  fun_prop (disch := positivity)

theorem energyDensity_integrableOn {d : ℝ} (hd : 0 < d) :
    IntegrableOn (energyDensity d) baseDomain :=
  ContinuousOn.integrableOn_compact baseDomain_isCompact (energyDensity_continuousOn hd)

private def pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

private theorem pairPlane_measurePreserving :
    MeasurePreserving pairPlaneEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

private theorem plane_integral_pair (f : Plane → ℝ) :
    (∫ z, f z) = ∫ q : ℝ × ℝ, f (vec2 q.1 q.2) :=
  (pairPlane_measurePreserving.integral_comp pairPlaneEquiv.measurableEmbedding f).symm

private theorem plane_integrable_pair (f : Plane → ℝ) :
    Integrable (fun q : ℝ × ℝ => f (vec2 q.1 q.2)) ↔ Integrable f :=
  pairPlane_measurePreserving.integrable_comp_emb pairPlaneEquiv.measurableEmbedding

private theorem plane_setIntegral_horizontal {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ t : ℝ, ∫ y in {y : ℝ | vec2 y t ∈ S}, f (vec2 y t) := by
  rw [← integral_indicator hS, plane_integral_pair]
  rw [Measure.volume_eq_prod, integral_prod_symm _
    (by simpa only [Measure.volume_eq_prod] using
      (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with t
  have hm : MeasurableSet {y : ℝ | vec2 y t ∈ S} :=
    hS.preimage (pairPlaneEquiv.measurable.comp (measurable_id.prodMk measurable_const))
  rw [← integral_indicator hm]
  rfl

private theorem plane_setIntegral_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane,
      z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    (∫ z in S, f z) = ∫ t in s, ∫ y in Icc (l t) (u t), f (vec2 y t) := by
  rw [plane_setIntegral_horizontal hS hf, ← integral_indicator hs]
  congr 1
  funext t
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht]
    apply setIntegral_congr_set
    filter_upwards with y
    apply propext
    simpa only [vec2_zero, vec2_one, ht, true_and] using heq (vec2 y t)
  · rw [Set.indicator_of_notMem ht]
    have he : {y : ℝ | vec2 y t ∈ S} = ∅ := by
      ext y
      simpa [vec2_zero, vec2_one, ht] using heq (vec2 y t)
    simp [he]

theorem energyIntegral_eq_wedgeCost {d : ℝ} (hd : 0 < d) :
    energyIntegral d = RationalCoefficients.wedgeCost d := by
  unfold energyIntegral RationalCoefficients.wedgeCost
  congr 1
  rw [plane_setIntegral_horizontal_interval (s := Icc (0:ℝ) (1/2))
    (l := fun t => -radius t/2) (u := fun t => radius t/2)
    baseDomain_isCompact.measurableSet (energyDensity_integrableOn hd)
    measurableSet_Icc baseDomain_mem_iff]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  let f : ℝ → ℝ := fun r => ∫ y in (-r/2)..(r/2),
    ((y^2/(4*(r+d)^2) + r*(r+2*d)/(16*(r+d)^2))^2 +
      (1/2)*(y/(2*(r+d)))^2)
  have he : (∫ t in (0:ℝ)..(1/2),
      ∫ y in Icc (-(radius t)/2) (radius t/2), energyDensity d (vec2 y t)) =
      ∫ t in (0:ℝ)..(1/2), f ((1/2)-t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) (1/2) := by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] using ht
    have hr : 0 ≤ radius t := by unfold radius; linarith [ht'.2]
    change (∫ y in Icc (-(radius t)/2) (radius t/2), energyDensity d (vec2 y t)) = f ((1/2)-t)
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -radius t/2 ≤ radius t/2)]
    dsimp [f, radius]
    apply intervalIntegral.integral_congr
    intro y _
    simp only [energyDensity, vec2_zero, vec2_one, a, b, radius]
    ring
  rw [he, intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self, sub_zero]
  rfl

theorem baseDomain_volume : volume.real baseDomain = (1/8:ℝ) := by
  have hi := plane_setIntegral_horizontal_interval (s := Icc (0:ℝ) (1/2))
    (l := fun t => -radius t/2) (u := fun t => radius t/2)
    baseDomain_isCompact.measurableSet
    (integrableOn_const (C := (1:ℝ)) baseDomain_isCompact.measure_lt_top.ne)
    measurableSet_Icc baseDomain_mem_iff
  have hv : volume.real baseDomain =
      ∫ t in Icc (0:ℝ) (1/2), max (radius t/2-(-radius t/2)) 0 := by
    simpa [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal'] using hi
  rw [hv]
  have he : (∫ t in Icc (0:ℝ) (1/2), max (radius t/2-(-radius t/2)) 0) =
      ∫ t in (0:ℝ)..(1/2), (1/2-t) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hrad : 0 ≤ radius t/2-(-radius t/2) := by unfold radius; linarith [ht.2]
    change max (radius t/2-(-radius t/2)) 0 = 1/2-t
    rw [max_eq_left hrad]
    unfold radius
    ring
  rw [he, intervalIntegral.integral_sub (f := fun _ : ℝ => (1/2:ℝ))
    (g := fun t : ℝ => t) intervalIntegrable_const
    (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
  norm_num

theorem field_component_bounds {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    |a d (z 0) (z 1)| ≤ 1/8 ∧ |b d (z 0) (z 1)| ≤ 1/4 := by
  have hw : 2*|z 0| ≤ radius (z 1) := hz
  have hr : 0 ≤ radius (z 1) := by linarith [abs_nonneg (z 0)]
  have hrd : 0 < radius (z 1)+d := by positivity
  have hay : 0 ≤ (z 0)^2/(4*(radius (z 1)+d)^2) := by positivity
  have hac : 0 ≤ radius (z 1)*(radius (z 1)+2*d)/(16*(radius (z 1)+d)^2) := by positivity
  have hy2 : (z 0)^2 ≤ (radius (z 1))^2/4 := by
    have h := (sq_le_sq₀ (abs_nonneg (z 0)) (show 0 ≤ radius (z 1)/2 by positivity)).2
      (show |z 0| ≤ radius (z 1)/2 by linarith)
    nlinarith [sq_abs (z 0)]
  have hden : 0 < 4*(radius (z 1)+d)^2 := by positivity
  have hay' : (z 0)^2/(4*(radius (z 1)+d)^2) ≤ 1/16 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg d, mul_nonneg hr hd.le]
  have hac' := (RationalCoefficients.angularA0_bounds hd hr).2
  change radius (z 1)*(radius (z 1)+2*d)/(16*(radius (z 1)+d)^2) ≤ 1/16 at hac'
  constructor
  · have ha : a d (z 0) (z 1) ≤ 0 := by unfold a; simp only [neg_div]; linarith
    rw [abs_of_nonpos ha]
    unfold a
    simp only [neg_div]
    linarith
  · unfold b
    rw [abs_div, abs_of_pos (show 0 < 2*(radius (z 1)+d) by positivity)]
    apply (div_le_iff₀ (show 0 < 2*(radius (z 1)+d) by positivity)).2
    linarith

theorem energyDensity_bounds {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    0 ≤ energyDensity d z ∧ energyDensity d z ≤ 3/64 := by
  obtain ⟨ha,hb⟩ := field_component_bounds hd hz
  have ha2 : (a d (z 0) (z 1))^2 ≤ (1/8:ℝ)^2 := by
    nlinarith [(sq_le_sq₀ (abs_nonneg (a d (z 0) (z 1))) (by norm_num)).2 ha,
      sq_abs (a d (z 0) (z 1))]
  have hb2 : (b d (z 0) (z 1))^2 ≤ (1/4:ℝ)^2 := by
    nlinarith [(sq_le_sq₀ (abs_nonneg (b d (z 0) (z 1))) (by norm_num)).2 hb,
      sq_abs (b d (z 0) (z 1))]
  unfold energyDensity
  exact ⟨by positivity, by linarith⟩

end RationalEnergy

namespace SlopeRational

theorem energyIntegral_tendsto :
    Tendsto energyIntegral (𝓝[>] (0:ℝ)) (𝓝 (17/15360:ℝ)) := by
  apply RationalCoefficients.wedgeCost_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (RationalEnergy.energyIntegral_eq_wedgeCost hd).symm

end SlopeRational

end

end OAI
