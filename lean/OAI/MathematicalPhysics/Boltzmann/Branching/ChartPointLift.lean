import OAI.MathematicalPhysics.Boltzmann.Collision.SheetGain

namespace OAI

section

/-!
# The normalized gain as a measure on chart coordinates

This measure retains the incoming velocity and both plane coordinates. Its
restriction equals the chart gain, so countable shell
estimates concern the full normalized kernel of the manuscript.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

abbrev Coordinates := Velocity × (ℝ × ℝ)

@[fun_prop] theorem measurable_transverse : Measurable transverse := by
  simpa only [Function.comp_def, split_apply] using measurable_snd.comp split.measurable

@[fun_prop] theorem measurable_axial : Measurable axial := by
  simpa only [Function.comp_def, split_apply] using measurable_fst.comp split.measurable

theorem measurable_point (v : Velocity) :
    Measurable (fun y : Coordinates => chart v y.1 y.2.1 y.2.2) := by
  have hn : Measurable (fun p : Velocity => normal v p) :=
    measurable_transverse.comp (measurable_const.sub measurable_id)
  have ha : Measurable (fun p : Velocity => axial (v - p)) :=
    measurable_axial.comp (measurable_const.sub measurable_id)
  have hj : Measurable (fun p : Transverse × ℝ => PlaneChart.join p.1 p.2) :=
    SheetMeasures.join.measurable
  have hf : Measurable (fun y : Coordinates =>
      TransverseLine.line (TransverseAverage.direction (normal v y.1))
        (offset v y.1 - PlaneChart.slope v y.1 * y.2.1) y.2.2) := by
    unfold TransverseLine.line TransverseLine.quarterTurn offset PlaneChart.slope
    unfold TransverseAverage.direction
    fun_prop
  exact hj.comp (hf.prodMk (measurable_const.add (measurable_fst.comp measurable_snd)))

theorem measurable_H (q : ℝ) : Measurable (H q) := by
  unfold H singularity
  fun_prop

theorem measurable_W (q : ℝ) : Measurable (W q) := by
  unfold W singularity
  fun_prop

def density (h : Velocity → ℝ≥0∞) (v : Velocity) (y : Coordinates) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (‖normal v y.1‖⁻¹) * h (chart v y.1 y.2.1 y.2.2)

theorem measurable_density {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity) :
    Measurable (density h v) := by
  have hn : Measurable (fun y : Coordinates => normal v y.1) :=
    measurable_transverse.comp (measurable_const.sub measurable_fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (hh.comp (measurable_point v))

def measure (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity) :
    Measure Coordinates :=
  (c.prod (volume.prod volume)).withDensity (density h v)

theorem region_eq_measure (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) :
    chartRegionGain c h v S = measure c h v S := by
  classical
  rw [measure, withDensity_apply _ hS, ← lintegral_indicator hS]
  rw [lintegral_prod _ ((measurable_density hh v).indicator hS).aemeasurable]
  have hi (p : Velocity) :
      (∫⁻ zs : ℝ × ℝ, S.indicator (density h v) (p, zs) ∂(volume.prod volume)) =
        ∫⁻ z : ℝ, ∫⁻ s : ℝ, S.indicator (density h v) (p, (z, s)) :=
    lintegral_prod _ (((measurable_density hh v).indicator hS).comp
      measurable_prodMk_left).aemeasurable
  simp_rw [hi]
  have he : ∀ p z s, S.indicator (density h v) (p, (z, s)) =
      2 * (ENNReal.ofReal (‖normal v p‖⁻¹) *
        S.indicator (fun y => h (chart v y.1 y.2.1 y.2.2)) (p, (z, s))) := by
    intro p z s
    by_cases hm : (p, (z, s)) ∈ S
    · simp only [indicator_of_mem hm, density, mul_assoc]
    · simp only [indicator_of_notMem hm, mul_zero]
  simp_rw [he, lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

def normalizedMeasure (c : Measure Velocity) (q : ℝ) (v : Velocity) : Measure Coordinates :=
  measure c (fun ξ => ENNReal.ofReal (H q ξ / H q v)) v

theorem normalized_region_eq (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {S : Set Coordinates} (hS : MeasurableSet S) :
    normalizedChartRegionGain c q v S = normalizedMeasure c q v S :=
  region_eq_measure c ((measurable_H q).div_const _ |>.ennreal_ofReal) v hS

theorem total_eq (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) :
    chartGain c h v = measure c h v univ := by
  simpa only [chartRegionGain, indicator_univ, chartGain] using
    region_eq_measure c hh v MeasurableSet.univ

theorem normalized_total_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    normalizedChartGain c q v = normalizedMeasure c q v univ :=
  total_eq c ((measurable_H q).div_const _ |>.ennreal_ofReal) v

theorem measure_mono_incoming {c d : Measure Velocity} (hcd : c ≤ d)
    (h : Velocity → ℝ≥0∞) (v : Velocity) : measure c h v ≤ measure d h v := by
  apply Measure.le_iff.mpr
  intro S hS
  simp only [measure, withDensity_apply _ hS]
  exact lintegral_mono' (Measure.restrict_mono_measure
    (Measure.prod_mono hcd le_rfl) S) (fun _ => le_rfl)

theorem measure_smul (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (a • c) h v = a • measure c h v := by
  rw [measure, Measure.prod_smul_left, withDensity_smul_measure]
  rfl

theorem measure_add (c d : Measure Velocity) [SFinite c] [SFinite d]
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (c + d) h v = measure c h v + measure d h v := by
  rw [measure, Measure.add_prod, withDensity_add_measure]
  rfl

theorem measure_withDensity (c : Measure Velocity) {w h : Velocity → ℝ≥0∞}
    (hw : Measurable w) (hh : Measurable h) (v : Velocity) :
    measure (c.withDensity w) h v =
      (c.prod (volume.prod volume)).withDensity (fun y => w y.1 * density h v y) := by
  rw [measure, prod_withDensity_left hw]
  exact (withDensity_mul _ (hw.comp measurable_fst) (measurable_density hh v)).symm

/-- A pointwise comparison, integrated without losing the coordinate restriction. -/
theorem restriction_comparison (c : Measure Velocity) {w h k : Velocity → ℝ≥0∞}
    (hw : Measurable w) (hk : Measurable k) (v : Velocity) (a : ℝ≥0∞)
    {S T : Set Coordinates} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hp : ∀ y, S.indicator (density h v) y ≤
      a * (w y.1 * T.indicator (density k v) y)) :
    measure c h v S ≤ a * measure (c.withDensity w) k v T := by
  rw [measure_withDensity c hw hk v]
  rw [measure, withDensity_apply _ hS, withDensity_apply _ hT,
    ← lintegral_indicator hS, ← lintegral_indicator hT]
  simp only [indicator_mul_right]
  have hm : Measurable (fun y : Coordinates => w y.1 * T.indicator (density k v) y) :=
    (hw.comp measurable_fst).mul ((measurable_density hk v).indicator hT)
  rw [← lintegral_const_mul a hm]
  apply lintegral_mono
  intro y
  exact hp y

theorem measure_restrict_incoming (c : Measure Velocity) [SFinite c]
    (h : Velocity → ℝ≥0∞) (v : Velocity) {A : Set Velocity} (hA : MeasurableSet A) :
    measure (c.restrict A) h v = (measure c h v).restrict (A ×ˢ univ) := by
  rw [measure, Measure.restrict_prod_eq_prod_univ, ← restrict_withDensity (hA.prod .univ)]
  rfl

theorem normalized_restrict_incoming (c : Measure Velocity) [SFinite c]
    (q : ℝ) (v : Velocity) {A : Set Velocity} (hA : MeasurableSet A) :
    normalizedMeasure (c.restrict A) q v = (normalizedMeasure c q v).restrict (A ×ˢ univ) :=
  measure_restrict_incoming c _ v hA

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Joint measurability of the collision-plane chart and normalized density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_joint_point : Measurable (fun p : Velocity × Coordinates =>
    chart p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hj : Measurable (fun p : Transverse × ℝ => PlaneChart.join p.1 p.2) :=
    SheetMeasures.join.measurable
  have hf : Measurable (fun p : Velocity × Coordinates =>
      TransverseLine.line (TransverseAverage.direction (normal p.1 p.2.1))
        (offset p.1 p.2.1-PlaneChart.slope p.1 p.2.1*p.2.2.1) p.2.2.2) := by
    unfold TransverseLine.line TransverseLine.quarterTurn offset PlaneChart.slope
    unfold TransverseAverage.direction normal
    fun_prop
  exact hj.comp (hf.prodMk ((measurable_axial.comp measurable_fst).add
    measurable_snd.snd.fst))

theorem measurable_joint_normalized_density (q : ℝ) :
    Measurable (fun p : Velocity × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1)) p.1 p.2) := by
  have hn : Measurable (fun p : Velocity × Coordinates => normal p.1 p.2.1) :=
    measurable_transverse.comp (measurable_fst.sub measurable_snd.fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (((measurable_H q).comp measurable_joint_point).div
      ((measurable_H q).comp measurable_fst)).ennreal_ofReal

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Pulling the joint chart through a kinetic base projection -/

noncomputable section
open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ChartKernel
variable {X : Type*} [MeasurableSpace X]

theorem measurable_lifted_density (q : ℝ) :
    Measurable (fun p : (X × Velocity) × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1.2)) p.1.2 p.2) := by
  let f : (X × Velocity) × Coordinates → Velocity × Coordinates := fun p => (p.1.2,p.2)
  have hf : Measurable f := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def,f] using (measurable_joint_normalized_density q).comp hf

theorem measurable_lifted_point : Measurable (fun p : (X × Velocity) × Coordinates =>
    PlaneChart.chart p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : (X × Velocity) × Coordinates → Velocity × Coordinates := fun p => (p.1.2,p.2)
  have hf : Measurable f := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def,f] using measurable_joint_point.comp hf

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
