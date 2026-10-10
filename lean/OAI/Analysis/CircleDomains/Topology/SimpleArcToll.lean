import OAI.Analysis.CircleDomains.Topology.PathTolls
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic

namespace OAI

/-! An injective arc pays each boundary weight at most once. The payment
is bounded by the actual atomic measure on any set containing the arc. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def atomicBoundaryMeasure {X : Type*} [MeasurableSpace X] (m : X → ℝ≥0∞) : Measure X :=
  Measure.sum (fun x => m x • Measure.dirac x)

theorem atomicBoundaryMeasure_apply {X : Type*} [MeasurableSpace X]
    (m : X → ℝ≥0∞) {S : Set X} (hS : MeasurableSet S) :
    atomicBoundaryMeasure m S = ∑'x, S.indicator m x := by
  classical
  rw [atomicBoundaryMeasure, Measure.sum_apply _ hS]
  apply tsum_congr
  intro x
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

theorem atomicBoundaryMeasure_null {X : Type*} [MeasurableSpace X]
    (m : X → ℝ≥0∞) {S : Set X} (hS : MeasurableSet S)
    (hm : ∀x ∈ S, m x = 0) : atomicBoundaryMeasure m S = 0 := by
  rw [atomicBoundaryMeasure_apply m hS]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx, hm x hx]
  · exact indicator_of_notMem hx m

theorem simple_arc_boundary_toll_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (γ : C(PathTime, X)) (hinj : Injective γ) (m : X → ℝ≥0∞)
    {S : Set X} (hS : MeasurableSet S) (hγ : range γ ⊆ S) :
    boundaryToll γ m ≤ atomicBoundaryMeasure m S := by
  rw [boundaryToll, atomicBoundaryMeasure_apply m hS]
  calc
    (∑'t, m (γ t)) = ∑'t, S.indicator m (γ t) := by
      apply tsum_congr
      intro t
      rw [indicator_of_mem (hγ (mem_range_self t))]
    _ ≤ ∑'x, S.indicator m x := ENNReal.tsum_comp_le_tsum_of_injective hinj _

end CircleDomainRigidity

end

end OAI
