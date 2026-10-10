import OAI.MathematicalPhysics.Boltzmann.Branching.GainNonnegative
import OAI.MathematicalPhysics.Boltzmann.Branching.HotGainReduction
import OAI.MathematicalPhysics.Boltzmann.Branching.PowerDiskMixture
import Mathlib.Analysis.PSeries

namespace OAI

section

/-!
# Normalized truncated transverse weights

The positive disk mixture transfers the existing disk kernel expectation
bound to the truncated singular density needed by the quadratic hot gain.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.PowerDiskMixture

namespace BoltzmannNonuniqueness.HotDiskEstimate

def radiusMass (q D : ℝ) : ℝ := Real.pi * q / (2 - q) * D ^ (2 - q)

def cutoffMass (q D : ℝ) : ℝ := boundaryMass q D + radiusMass q D

def cutoffLaw (q D : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (cutoffDensity q D p))

theorem radiusMass_nonneg {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 ≤ D) :
    0 ≤ radiusMass q D := by
  unfold radiusMass
  positivity

theorem cutoffMass_pos {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 < D) :
    0 < cutoffMass q D := by
  have hb : 0 < boundaryMass q D := by
    unfold boundaryMass
    positivity
  exact add_pos_of_pos_of_nonneg hb (radiusMass_nonneg hq₁ hq₂ hD.le)

theorem mixing_mass {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 ≤ D) :
    (∫⁻ a in Ioc 0 D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a)) =
      ENNReal.ofReal (radiusMass q D) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (PowerDiskMixture.integrableOn_mixingDensity hq₂ hD),
    PowerDiskMixture.integral_mixingDensity hq₂ hD]
  · rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact PowerDiskMixture.mixingDensity_nonneg hq₁ ha.1.le

theorem cutoffLaw_mass {q D : ℝ} (hq₁ : 0 < q) (hq₂ : q < 2) (hD : 0 < D) :
    cutoffLaw q D univ = ENNReal.ofReal (cutoffMass q D) := by
  rw [cutoffLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := lintegral_cutoff_mixture hq₁ hD (fun _ => 1) measurable_const
  simp only [mul_one, lintegral_diskDensity hD] at h
  rw [h]
  have hi : (∫⁻ a in Ioc (0 : ℝ) D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a) *
      (∫⁻ p : Transverse, ENNReal.ofReal (diskDensity a p))) =
      ∫⁻ a in Ioc (0 : ℝ) D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    rw [lintegral_diskDensity ha.1, mul_one]
  rw [hi, mixing_mass hq₁.le hq₂ hD.le, ← ENNReal.ofReal_add
    (boundaryMass_nonneg q hD.le) (radiusMass_nonneg hq₁.le hq₂ hD.le)]
  rfl

theorem cutoff_kernel_bound {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D)
    {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂cutoffLaw q D) ≤
      ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hd (a : ℝ) (ha : 0 < a) :
      (∫⁻ p, ENNReal.ofReal (diskDensity a p) * extendedKernel q v p) ≤
        ENNReal.ofReal (expectationConstant q / ‖v‖) := by
    have h := uniformDisk_extendedKernel_lintegral_le hq₁ hq₂ ha hv
    rw [uniformDiskLaw, lintegral_withDensity_eq_lintegral_mul volume
      (measurable_diskDensity_fixed a).ennreal_ofReal (measurable_extendedKernel q v)] at h
    exact h
  have hm : Measurable (fun p => ENNReal.ofReal (cutoffDensity q D p)) := by
    unfold cutoffDensity
    apply Measurable.ennreal_ofReal
    apply Measurable.indicator _ measurableSet_ball
    fun_prop
  rw [cutoffLaw, lintegral_withDensity_eq_lintegral_mul volume hm (measurable_extendedKernel q v)]
  change (∫⁻ p, ENNReal.ofReal (cutoffDensity q D p) * extendedKernel q v p) ≤ _
  rw [lintegral_cutoff_mixture (by linarith : 0 < q) hD _ (measurable_extendedKernel q v)]
  calc
    _ ≤ ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (expectationConstant q / ‖v‖) +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a) *
          ENNReal.ofReal (expectationConstant q / ‖v‖) := by
      apply add_le_add (mul_le_mul' le_rfl (hd D hD))
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact mul_le_mul' le_rfl (hd a ha.1)
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        mixing_mass (by linarith : 0 ≤ q) hq₂ hD.le, ← add_mul,
        ← ENNReal.ofReal_add (boundaryMass_nonneg q hD.le)
          (radiusMass_nonneg (by linarith) hq₂ hD.le)]
      rfl

def normalizedCutoff (q D : ℝ) : Measure Transverse :=
  (ENNReal.ofReal (cutoffMass q D))⁻¹ • cutoffLaw q D

theorem normalizedCutoff_isProbabilityMeasure {q D : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) :
    IsProbabilityMeasure (normalizedCutoff q D) := by
  constructor
  rw [normalizedCutoff, Measure.smul_apply, smul_eq_mul,
    cutoffLaw_mass (by linarith) hq₂ hD]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (cutoffMass_pos (by linarith) hq₂ hD)))
    ENNReal.ofReal_ne_top

theorem normalizedCutoff_absolutelyContinuous (q D : ℝ) :
    normalizedCutoff q D ≪ volume := by
  intro s hs
  rw [normalizedCutoff, Measure.smul_apply]
  have hc : cutoffLaw q D s = 0 := withDensity_absolutelyContinuous volume _ hs
  rw [hc, smul_zero]

theorem normalizedCutoff_kernel_bound {q D : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂normalizedCutoff q D) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [normalizedCutoff, lintegral_smul_measure]
  simp only [smul_eq_mul]
  apply (mul_le_mul' le_rfl (cutoff_kernel_bound hq₁ hq₂ hD hv)).trans_eq
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (cutoffMass_pos (by linarith) hq₂ hD)))
    ENNReal.ofReal_ne_top, one_mul]

/-- The geometric slice estimate applies uniformly to the normalized hot measure. -/
theorem normalizedCutoff_geometric_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R
      ∂(normalizedCutoff q D).prod ρ) ≤ ENNReal.ofReal (geometricTotalConstant q * R ^ 2) :=
  geometric_total_of_kernel_bound hq₁ hq₂ hR hv t (normalizedCutoff q D) ρ
    ((normalizedCutoff_absolutelyContinuous q D).ae_le (ae_regularTransverse_volume hv))
    (normalizedCutoff_kernel_bound hq₁ hq₂ hD hv)

end BoltzmannNonuniqueness.HotDiskEstimate

end

end

section

/-!
# Collision-chart bounds for truncated hot weights

The transverse singular density is normalized explicitly. The axial factor is
normalized Lebesgue measure on a bounded interval. This supplies the geometric
ball estimate used in the polynomial shell summation.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotChartBalls

def intervalLaw (D : ℝ) : Measure ℝ := volume.restrict (Ioo (-D) D)

theorem intervalLaw_mass (D : ℝ) :
    intervalLaw D univ = ENNReal.ofReal (2 * D) := by
  simp only [intervalLaw, Measure.restrict_apply_univ, Real.volume_Ioo]
  congr 1
  ring

def normalizedInterval (D : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * D))⁻¹ • intervalLaw D

theorem normalizedInterval_isProbabilityMeasure {D : ℝ} (hD : 0 < D) :
    IsProbabilityMeasure (normalizedInterval D) := by
  constructor
  rw [normalizedInterval, Measure.smul_apply, smul_eq_mul, intervalLaw_mass]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

def rectangleLaw (q D : ℝ) : Measure Velocity :=
  ((cutoffLaw q D).prod (intervalLaw D)).map join

def normalizedRectangle (q D : ℝ) : Measure Velocity :=
  ((normalizedCutoff q D).prod (normalizedInterval D)).map join

theorem rectangle_eq_smul {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) :
    rectangleLaw q D =
      (ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (2 * D)) • normalizedRectangle q D := by
  have : IsFiniteMeasure (intervalLaw D) := by unfold intervalLaw; infer_instance
  have : IsProbabilityMeasure (normalizedInterval D) := normalizedInterval_isProbabilityMeasure hD
  have : SFinite ((ENNReal.ofReal (2 * D))⁻¹ • intervalLaw D) :=
    inferInstanceAs (SFinite (normalizedInterval D))
  unfold normalizedRectangle normalizedCutoff normalizedInterval
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ join.measurable.aemeasurable, smul_smul]
  have hc : ENNReal.ofReal (cutoffMass q D) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (cutoffMass_pos (by linarith) hq₂ hD))
  have hd : ENNReal.ofReal (2 * D) ≠ 0 := by positivity
  rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top,
    ENNReal.mul_inv_cancel hd ENNReal.ofReal_ne_top, mul_one, one_smul]
  rfl

theorem weight_ball_normalizedRectangle_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    chartRegionGain (normalizedRectangle q D) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have := normalizedInterval_isProbabilityMeasure hD
  have hs := normalizedCutoff_geometric_bound hq₁ hq₂ hD hR hv (axial v)
    (normalizedInterval D)
  unfold chartRegionGain
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂normalizedRectangle q D) ≤ _
  unfold normalizedRectangle
  rw [lintegral_map_equiv]
  exact mul_le_mul_right ((lintegral_mono (ballChartFiber_le_slice (by linarith) q v)).trans hs) 2

theorem weight_ball_rectangle_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    ChartKernel.measure (rectangleLaw q D) (weightRatio q v) v (ballRegion v R) ≤
      (ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (2 * D)) *
        (2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2)) := by
  rw [rectangle_eq_smul hq₁ hq₂ hD, measure_smul, Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul' le_rfl
  rw [← region_eq_measure _ (UniformGain.measurable_weightRatio q v) _
    (UniformGain.measurableSet_ballRegion v R)]
  exact weight_ball_normalizedRectangle_bound hq₁ hq₂ hD hR hv

def massConstant (q : ℝ) : ℝ := 2 * Real.pi + Real.pi * q / (2 - q)

theorem massConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < massConstant q := by unfold massConstant; positivity

theorem cutoffMass_le {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 1 ≤ D) :
    cutoffMass q D ≤ massConstant q * D ^ 2 := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hneg : D ^ (-q) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith : -q ≤ 0))
  have hsmall : D ^ (2 - q) ≤ D ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith : 2 - q ≤ (2 : ℝ)))
  have hb : PowerDiskMixture.boundaryMass q D ≤ 2 * Real.pi * D ^ 2 := by
    unfold PowerDiskMixture.boundaryMass
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1 + D ^ (-q) ≤ 2) Real.pi_pos.le)
      (sq_nonneg D)
  have hr : radiusMass q D ≤ (Real.pi * q / (2 - q)) * D ^ 2 := by
    unfold radiusMass
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  unfold cutoffMass massConstant
  nlinarith

end BoltzmannNonuniqueness.HotChartBalls

end

end

section

/-! # The truncated hot rectangle in physical velocity coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotChartBalls

namespace BoltzmannNonuniqueness.HotRectangleDensity

def rectangle (D : ℝ) : Set Velocity :=
  {p | ‖transverse p‖ < D ∧ axial p ∈ Ioo (-D) D}

def weight (q D : ℝ) : Velocity → ℝ≥0∞ :=
  (rectangle D).indicator (fun p => ENNReal.ofReal (W q p))

theorem measurableSet_rectangle (D : ℝ) : MeasurableSet (rectangle D) :=
  (measurableSet_lt ChartKernel.measurable_transverse.norm measurable_const).inter
    (ChartKernel.measurable_axial measurableSet_Ioo)

theorem measurable_weight (q D : ℝ) : Measurable (weight q D) :=
  ((ChartKernel.measurable_W q).ennreal_ofReal).indicator (measurableSet_rectangle D)

theorem join_measurePreserving :
    MeasurePreserving join ((volume : Measure Transverse).prod volume) volume := by
  have hs : MeasurePreserving split.symm
      ((volume : Measure ℝ).prod (volume : Measure Transverse)) volume := by
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.symm split split_measurePreserving)
  exact (Measure.measurePreserving_swap (μ := volume (α := Transverse))
    (ν := volume (α := ℝ))).trans hs

theorem join_withDensity (w : Velocity → ℝ≥0∞) :
    (((volume : Measure Transverse).prod volume).withDensity (fun p => w (join p))).map join =
      volume.withDensity w := by
  ext s hs
  rw [Measure.map_apply join.measurable hs, withDensity_apply _ (hs.preimage join.measurable),
    withDensity_apply _ hs, ← lintegral_indicator (hs.preimage join.measurable),
    ← lintegral_indicator hs,
    MeasurePreserving.lintegral_map_equiv (s.indicator w) join join_measurePreserving]
  apply lintegral_congr
  intro p
  rfl

theorem rectangleLaw_eq_density (q D : ℝ) :
    rectangleLaw q D = volume.withDensity (weight q D) := by
  have hm : Measurable (fun p : Transverse =>
      ENNReal.ofReal (PowerDiskMixture.cutoffDensity q D p)) := by
    unfold PowerDiskMixture.cutoffDensity
    apply Measurable.ennreal_ofReal
    apply Measurable.indicator _ measurableSet_ball
    fun_prop
  have hprod : (cutoffLaw q D).prod (intervalLaw D) =
      ((volume : Measure Transverse).prod volume).withDensity (fun p => weight q D (join p)) := by
    unfold cutoffLaw intervalLaw
    have hi : Measurable ((Ioo (-D) D).indicator (1 : ℝ → ℝ≥0∞)) :=
      measurable_const.indicator measurableSet_Ioo
    rw [← withDensity_indicator_one measurableSet_Ioo, prod_withDensity hm hi]
    congr 1
    funext p
    have ht : transverse (join p) = p.1 := PlaneChart.transverse_join _ _
    have ha : axial (join p) = p.2 := PlaneChart.axial_join _ _
    simp only [PowerDiskMixture.cutoffDensity, weight, rectangle, indicator_apply,
      mem_ofPred_eq, ht, ha, W, singularity]
    split_ifs <;> simp_all
  rw [rectangleLaw, hprod, join_withDensity]

theorem norm_ball_subset_rectangle {D : ℝ} {p : Velocity} (hp : ‖p‖ < D) :
    p ∈ rectangle D := by
  have ht : ‖transverse p‖ ≤ ‖p‖ := by
    nlinarith [norm_sq_split p, sq_nonneg (axial p), norm_nonneg (transverse p), norm_nonneg p]
  have ha : |axial p| ≤ ‖p‖ := by
    nlinarith [norm_sq_split p, sq_nonneg ‖transverse p‖, sq_abs (axial p),
      abs_nonneg (axial p), norm_nonneg p]
  exact ⟨ht.trans_lt hp, abs_lt.mp (ha.trans_lt hp)⟩

end BoltzmannNonuniqueness.HotRectangleDensity

end

end

section

/-! # Restricting the mixed hot gain to polynomial shells -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotMixedGain

def mixedMeasure (q : ℝ) (v : Velocity) : Measure Coordinates :=
  ChartKernel.measure (volume.withDensity (fun p => ENNReal.ofReal (H q p)))
    (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v

theorem pointwise_bound (q : ℝ) (v : Velocity) (y : Coordinates) {A : ℝ}
    (h : Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) *
        (polynomial y.1)⁻¹ ≤ A) :
    ENNReal.ofReal (H q y.1) *
      density (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v y ≤
    ENNReal.ofReal A * (ENNReal.ofReal (W q y.1) * density (weightRatio q v) v y) := by
  by_cases hn : normal v y.1 = 0
  · simp [density, hn]
  · have hw₁ := (W_pos q y.1).le
    have hw₂ := (W_pos q (chart v y.1 y.2.1 y.2.2)).le
    have hwv := (W_pos q v).le
    have hr : H q y.1 * (G q (chart v y.1 y.2.1 y.2.2) / G q v) ≤
        A * (W q y.1 * (W q (chart v y.1 y.2.1 y.2.2) / W q v)) := by
      rw [mixed_plane_weight q _ _ _ (chart_on_plane _ _ _ _ hn)]
      have hw : 0 ≤ W q y.1 * W q (chart v y.1 y.2.1 y.2.2) / W q v := by
        positivity
      convert mul_le_mul_of_nonneg_right h hw using 1
      ring
    have hp := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (H_nonneg q y.1),
      ENNReal.ofReal_mul' (by positivity : 0 ≤ W q y.1 *
        (W q (chart v y.1 y.2.1 y.2.2) / W q v)),
      ENNReal.ofReal_mul (W_pos q y.1).le] at hp
    have he := mul_le_mul_left hp (2 * ENNReal.ofReal (‖normal v y.1‖⁻¹))
    simpa only [density, weightRatio, mul_assoc, mul_left_comm, mul_comm] using he

theorem restricted_bound (q D : ℝ) (v : Velocity) {S : Set Coordinates}
    (hS : MeasurableSet S) (hball : S ⊆ ballRegion v D)
    (hp : ∀ y ∈ S, ‖y.1‖ < D + 1) {A : ℝ}
    (hA : ∀ y ∈ S,
      Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) *
        (polynomial y.1)⁻¹ ≤ A) :
    mixedMeasure q v S ≤ ENNReal.ofReal A *
      ChartKernel.measure (rectangleLaw q (D + 1)) (weightRatio q v) v (ballRegion v D) := by
  have hG : Measurable (fun ξ => ENNReal.ofReal (G q ξ / G q v)) :=
    ((measurable_G q).div_const _).ennreal_ofReal
  rw [mixedMeasure, measure_withDensity volume (measurable_H q).ennreal_ofReal hG v,
    HotRectangleDensity.rectangleLaw_eq_density,
    measure_withDensity volume (HotRectangleDensity.measurable_weight q (D + 1))
      (measurable_weightRatio q v) v,
    withDensity_apply _ hS, withDensity_apply _ (measurableSet_ballRegion v D),
    ← lintegral_indicator hS, ← lintegral_indicator (measurableSet_ballRegion v D),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  dsimp only
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (hball hy)]
    have hm := HotRectangleDensity.norm_ball_subset_rectangle (hp y hy)
    rw [HotRectangleDensity.weight, indicator_of_mem hm]
    exact pointwise_bound q v y (hA y hy)
  · rw [indicator_of_notMem hy]
    exact bot_le

def core (v : Velocity) : Set Coordinates := {y | radius v y ≤ 2}

theorem core_bound (q : ℝ) (v : Velocity) :
    mixedMeasure q v (core v) ≤
      ChartKernel.measure (rectangleLaw q 3) (weightRatio q v) v (ballRegion v 2) := by
  have h := restricted_bound q 2 v (measurableSet_le (measurable_radius v) measurable_const)
    (fun y hy => (le_add_of_nonneg_left (norm_nonneg y.1)).trans hy)
    (fun y hy => by
      have hk := norm_nonneg (chart v y.1 y.2.1 y.2.2 - v)
      change ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ 2 at hy
      linarith)
    (A := 1) (fun y _ => by
      calc
        _ ≤ (polynomial y.1)⁻¹ := mul_le_of_le_one_left
          (inv_nonneg.mpr (polynomial_pos y.1).le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
        _ ≤ 1 := HotShellWeight.polynomial_inv_le_one y.1)
  norm_num at h
  exact h

theorem shell_bound (q : ℝ) (v : Velocity) {R : ℝ} (hR : 0 < R) :
    mixedMeasure q v (shell v R) ≤ ENNReal.ofReal (HotShellWeight.constant / R ^ 8) *
      ChartKernel.measure (rectangleLaw q (2 * R + 1)) (weightRatio q v) v (ballRegion v (2 * R)) := by
  apply restricted_bound q (2 * R) v (measurableSet_shell v R) (shell_subset_ball v R)
  · intro y hy
    have hk := norm_nonneg (chart v y.1 y.2.1 y.2.2 - v)
    change _ ∧ ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ 2 * R at hy
    linarith [hy.2]
  · intro y hy
    apply HotShellWeight.decay hR
    have hs := shell_alternative y.1 (chart v y.1 y.2.1 y.2.2 - v) hy.1
    simpa only [companionVelocity, sub_eq_add_neg, add_assoc] using hs

end BoltzmannNonuniqueness.HotMixedGain

end

end

section

/-! # Summation of the mixed hot gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotMixedGain
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotTotal

def shellConstant (q : ℝ) : ℝ :=
  432 * HotShellWeight.constant * massConstant q * geometricTotalConstant q

theorem geometricTotalConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < geometricTotalConstant q := by
  unfold geometricTotalConstant
  exact mul_pos (by positivity) (geometricConstant_pos hq₁ hq₂)

theorem shellConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < shellConstant q := by
  have := HotShellWeight.constant_pos
  have := massConstant_pos hq₁ hq₂
  have := geometricTotalConstant_pos hq₁ hq₂
  unfold shellConstant
  positivity

theorem shell_real_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 1 ≤ R) :
    (HotShellWeight.constant / R ^ 8) *
        ((cutoffMass q (2 * R + 1) * (2 * (2 * R + 1))) *
          (2 * (geometricTotalConstant q * (2 * R) ^ 2))) ≤ shellConstant q / R ^ 3 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hD : 1 ≤ 2 * R + 1 := by linarith
  have hM := massConstant_pos hq₁ hq₂
  have hG := geometricTotalConstant_pos hq₁ hq₂
  have hc := HotShellWeight.constant_pos
  have hb := cutoffMass_le hq₁ hq₂ hD
  have hs : cutoffMass q (2 * R + 1) ≤ massConstant q * (3 * R) ^ 2 := by
    apply hb.trans
    gcongr
    linarith
  calc
    _ ≤ (HotShellWeight.constant / R ^ 8) *
        ((massConstant q * (3 * R) ^ 2 * (2 * (3 * R))) *
          (2 * (geometricTotalConstant q * (2 * R) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hs (by linarith) (by positivity) (by positivity)
    _ = shellConstant q / R ^ 3 := by
      unfold shellConstant
      field_simp
      ring

theorem mixed_shell_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    mixedMeasure q v (shell v R) ≤ ENNReal.ofReal (shellConstant q / R ^ 3) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hm := cutoffMass_pos (by linarith : 0 ≤ q) hq₂ (by linarith : 0 < 2 * R + 1)
  have hg := geometricTotalConstant_pos hq₁ hq₂
  have hc := HotShellWeight.constant_pos
  have h := (shell_bound q v hRp).trans (mul_le_mul' le_rfl
    (weight_ball_rectangle_bound hq₁ hq₂ (by linarith) (by linarith) hv))
  have hh := ENNReal.ofReal_le_ofReal (shell_real_bound hq₁ hq₂ hR)
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ HotShellWeight.constant / R ^ 8),
    ENNReal.ofReal_mul (by positivity : 0 ≤ cutoffMass q (2 * R + 1) * (2 * (2 * R + 1))),
    ENNReal.ofReal_mul hm.le, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] at hh
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] at h hh
  exact h.trans hh

def baseBound (q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (cutoffMass q 3) * ENNReal.ofReal 6) *
    (2 * ENNReal.ofReal (geometricTotalConstant q * 2 ^ (2 : ℕ)))

def bound (q : ℝ) : ℝ≥0∞ := baseBound q +
  ∑' n : ℕ, ENNReal.ofReal (shellConstant q / ((n : ℝ) + 1) ^ (3 : ℕ))

theorem bound_lt_top (q : ℝ) : bound q < ∞ := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))).comp_injective
      Nat.succ_injective
    simpa only [Function.comp_def, Nat.cast_succ] using h
  have hc : Summable (fun n : ℕ => shellConstant q / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    simpa only [mul_one_div] using hs.mul_left (shellConstant q)
  unfold bound baseBound
  exact ENNReal.add_lt_top.mpr ⟨by finiteness, hc.tsum_ofReal_lt_top⟩

theorem cover (v : Velocity) :
    (univ : Set Coordinates) ⊆ core v ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1) := by
  intro y _
  by_cases hr : radius v y ≤ 2
  · exact Or.inl hr
  · apply Or.inr
    have hr₂ : 2 < radius v y := lt_of_not_ge hr
    let n := Nat.floor (radius v y / 2)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hn : (n : ℝ) ≤ radius v y / 2 := Nat.floor_le (by linarith)
    have hn' : radius v y / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor <;> linarith

theorem mixed_total_bound {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {v : Velocity} (hv : transverse v ≠ 0) :
    mixedMeasure q v univ ≤ bound q := by
  have hb := (core_bound q v).trans (weight_ball_rectangle_bound
    (q := q) (D := 3) (R := 2) hq₁ hq₂ (by norm_num) (by norm_num) hv)
  have hbase : mixedMeasure q v (core v) ≤ baseBound q := by
    simpa only [baseBound, show (2 : ℝ) * 3 = 6 by norm_num] using hb
  calc
    _ ≤ mixedMeasure q v (core v ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1)) :=
      measure_mono (cover v)
    _ ≤ mixedMeasure q v (core v) + ∑' n : ℕ,
        mixedMeasure q v (shell v ((n : ℝ) + 1)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ bound q := by
      apply add_le_add hbase
      apply ENNReal.tsum_le_tsum
      intro n
      exact mixed_shell_bound hq₁ hq₂ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hv

end BoltzmannNonuniqueness.HotTotal

end

end

section

/-!
# The quadratic hot-gain bound

The geometric shell estimates and their summation transfer through the
Carleman identity to the original hard-sphere collision variables.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.HotMixedGain

namespace BoltzmannNonuniqueness.HotApplication

theorem gain_G_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    chartGain c (fun ξ => ENNReal.ofReal (G q ξ)) v =
      ENNReal.ofReal (G q v) *
        chartGain c (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v := by
  have he : (fun ξ => ENNReal.ofReal (G q ξ)) =
      (fun ξ => ENNReal.ofReal (G q v) * ENNReal.ofReal (G q ξ / G q v)) := by
    funext ξ
    rw [← ENNReal.ofReal_mul (G_pos q v).le]
    congr 1
    field_simp [(G_pos q v).ne']
  rw [he, SheetApplication.gain_const_mul_right c _ v ENNReal.ofReal_ne_top]

theorem quadratic_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (H q ξ)) v ≤
      ENNReal.ofReal (H q v) * (ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q) := by
  filter_upwards [hcarleman _ _ (measurable_H q).ennreal_ofReal
    (measurable_G q).ennreal_ofReal, SheetApplication.ae_transverse_ne_zero] with v hcar hv
  have hm : nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
      (fun ξ => ENNReal.ofReal (G q ξ)) v ≤
      ENNReal.ofReal (G q v) * HotTotal.bound q := by
    rw [hcar, gain_G_eq, total_eq _ ((measurable_G q).div_const _ |>.ennreal_ofReal)]
    exact mul_le_mul' le_rfl (HotTotal.mixed_total_bound hq₁ hq₂ hv)
  have hc : ENNReal.ofReal (HotGainReduction.coefficient q v) * ENNReal.ofReal (G q v) =
      ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * ENNReal.ofReal (H q v) := by
    rw [← ENNReal.ofReal_mul (HotGainReduction.coefficient_nonneg q v),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (51 : ℕ))]
    apply congrArg ENNReal.ofReal
    unfold HotGainReduction.coefficient
    rw [mul_assoc, div_mul_cancel₀ _ (G_pos q v).ne']
  calc
    _ ≤ ENNReal.ofReal (HotGainReduction.coefficient q v) *
        (ENNReal.ofReal (G q v) * HotTotal.bound q) :=
      (HotGainReduction.quadratic_gain_le_mixed q v).trans (mul_le_mul' le_rfl hm)
    _ = _ := by rw [← mul_assoc, hc]; ac_rfl

def realBound (q : ℝ) : ℝ :=
  (ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q).toReal + 1

theorem realBound_pos (q : ℝ) : 0 < realBound q := by
  unfold realBound
  positivity

/-- Manuscript Lemma `lem:hot-bound`, for the fixed weight exponent `m = 100`. -/
theorem quadratic_gain_le_constant (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (H q ξ)) v ≤ ENNReal.ofReal (realBound q * H q v) := by
  have ht : ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (HotTotal.bound_lt_top q)).ne
  have hb : ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q ≤
      ENNReal.ofReal (realBound q) := by
    rw [realBound, ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal ht]
    exact le_add_of_nonneg_right zero_le
  filter_upwards [quadratic_gain_bound hcarleman hq₁ hq₂] with v hv
  apply hv.trans
  rw [mul_comm (realBound q), ENNReal.ofReal_mul (H_nonneg q v)]
  exact mul_le_mul' le_rfl hb

end BoltzmannNonuniqueness.HotApplication

end

end

section

/-! # The real-valued hot-gain estimate for the approximation equations -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotApplication
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRealGain

theorem quadratic_gain (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity,
      Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) ∧
      ∀ x : Position, gain (fun p => H q p.2) x v ≤ realBound q * H q v := by
  filter_upwards [quadratic_gain_le_constant hcarleman hq₁ hq₂] with v hv
  exact ⟨GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv,
    fun x => GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
      (mul_nonneg (realBound_pos q).le (H_nonneg q v)) v x hv⟩

theorem dominated_gain (hcarleman : Published.GPV2009CarlemanInput)
    {q A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w) (hbound : ∀ w, f w ≤ A * H q w) :
    ∀ᵐ v : Velocity,
      Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea) ∧
      ∀ x : Position, gain (fun p => f p.2) x v ≤ (A ^ 2 * realBound q) * H q v := by
  filter_upwards [quadratic_gain hcarleman hq₁ hq₂] with v hv
  have hscaled := GainOrder.integrable_const_mul A v hv.1
  refine ⟨GainOrder.integrable_of_le hm hf hbound v hscaled, ?_⟩
  intro x
  calc
    _ ≤ gain (fun p => A * H q p.2) x v := GainOrder.gain_mono hm hf hbound v x hscaled
    _ = A ^ 2 * gain (fun p => H q p.2) x v := GainOrder.gain_const_mul A (H q) v x
    _ ≤ A ^ 2 * (realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (hv.2 x) (sq_nonneg A)
    _ = _ := by ring

end BoltzmannNonuniqueness.HotRealGain

end

end

end OAI
