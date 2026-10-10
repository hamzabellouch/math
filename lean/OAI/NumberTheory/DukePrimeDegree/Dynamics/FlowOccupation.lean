import OAI.NumberTheory.DukePrimeDegree.Geometry.DiscreteMaximal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-!
# One-unit occupation observables

For a measurable measure-preserving flow, the time spent in a measurable
set during one unit interval is a measurable integrable observable. Its
space integral is exactly the measure of that set. Its discrete sums
are the occupation integrals on the corresponding integer intervals.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma integrable_one_indicator_comp
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {F : Z → Y} (hF : Measurable F)
    {E : Set Y} (hE : MeasurableSet E) :
    Integrable (fun z => E.indicator (fun _ => (1 : ℝ)) (F z)) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.indicator hE).comp hF).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : F z ∈ E <;> simp [hz]

def unitFlowOccupation {Y : Type*} (Φ : ℝ → Y → Y) (E : Set Y) (x : Y) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, E.indicator (fun _ => (1 : ℝ)) (Φ t x)

lemma measurable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Measurable (unitFlowOccupation Φ E) := by
  have hχ : Measurable (fun p : Y × ℝ =>
      E.indicator (fun _ => (1 : ℝ)) (Φ p.2 p.1)) :=
    (measurable_const.indicator hE).comp hΦ
  exact hχ.stronglyMeasurable.integral_prod_right'.measurable

lemma unitFlowOccupation_nonneg
    {Y : Type*} (Φ : ℝ → Y → Y) (E : Set Y) (x : Y) :
    0 ≤ unitFlowOccupation Φ E x := by
  apply integral_nonneg
  intro t
  exact indicator_nonneg (fun _ _ => zero_le_one) (Φ t x)

lemma unitFlowOccupation_le_one
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) : unitFlowOccupation Φ E x ≤ 1 := by
  have hF : Measurable (fun t => Φ t x) := hΦ.comp (measurable_const.prodMk measurable_id)
  have hi := integrable_one_indicator_comp (volume.restrict (Ioc (0 : ℝ) 1)) hF hE
  have h := integral_mono hi (integrable_const (1 : ℝ))
    (fun t => show E.indicator (fun _ => (1 : ℝ)) (Φ t x) ≤ 1 from by
      by_cases ht : Φ t x ∈ E <;> simp [ht])
  simpa [unitFlowOccupation, measureReal_def] using h

lemma integrable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Integrable (unitFlowOccupation Φ E) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_unitFlowOccupation hΦ hE).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (unitFlowOccupation_nonneg Φ E x)]
    exact unitFlowOccupation_le_one hΦ hE x

theorem integral_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) :
    ∫ x, unitFlowOccupation Φ E x ∂μ = μ.real E := by
  have hi := integrable_one_indicator_comp
    (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) hΦ hE
  change (∫ x, (∫ t in Ioc (0 : ℝ) 1,
    E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ∂μ) = _
  rw [integral_integral_swap hi]
  have heq (t : ℝ) : (∫ x, E.indicator (fun _ => (1 : ℝ)) (Φ t x) ∂μ) = μ.real E := by
    have hm : AEStronglyMeasurable (E.indicator (fun _ => (1 : ℝ))) (μ.map (Φ t)) := by
      rw [(hpres t).map_eq]
      exact (measurable_const.indicator hE).aestronglyMeasurable
    rw [← integral_map (hpres t).measurable.aemeasurable hm, (hpres t).map_eq,
      integral_indicator_const (1 : ℝ) hE]
    simp
  simp_rw [heq]
  simp [measureReal_def]

lemma intervalIntegrable_flow_indicator
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (a b : ℝ) :
    IntervalIntegrable (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr (isCompact_uIcc.measure_lt_top.ne)
  apply (intervalIntegrable_iff').mpr
  exact integrable_one_indicator_comp (volume.restrict (uIcc a b))
    (hΦ.comp (measurable_const.prodMk measurable_id)) hE

lemma flow_nat_iterate {Y : Type*} {Φ : ℝ → Y → Y}
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (n : ℕ) (x : Y) : (Φ 1)^[n] x = Φ n x := by
  induction n generalizing x with
  | zero => simpa using (hzero x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Nat.cast_add, Nat.cast_one,
      add_comm (n : ℝ) 1, hadd]

theorem birkhoffSum_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    {E : Set Y} (hE : MeasurableSet E) (n : ℕ) (x : Y) :
    birkhoffSum (Φ 1) (unitFlowOccupation Φ E) n x =
      ∫ t in (0 : ℝ)..(n : ℝ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
  have hterm (k : ℕ) : unitFlowOccupation Φ E ((Φ 1)^[k] x) =
      ∫ t in (k : ℝ)..(k + 1 : ℕ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
    rw [flow_nat_iterate hzero hadd]
    change (∫ t in Ioc (0 : ℝ) 1, E.indicator (fun _ => (1 : ℝ)) (Φ t (Φ k x))) = _
    simp_rw [← hadd]
    rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    have hs := intervalIntegral.integral_comp_add_right
      (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) (a := 0) (b := 1) (k : ℝ)
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
  simp_rw [birkhoffSum, hterm]
  simpa only [Nat.cast_zero] using
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ))
      (fun k _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          intervalIntegrable_flow_indicator hΦ hE x k (k + 1))

end DukePrimeDegree

end

end OAI
