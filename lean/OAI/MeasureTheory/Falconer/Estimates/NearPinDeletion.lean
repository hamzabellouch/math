import OAI.MeasureTheory.Falconer.Estimates.CellwisePairDeletion
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! # Near-parent pins are removed with their original source-cell weights -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

noncomputable def nearPinPairs (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ) :
    Set (X × Y) := ⋃ i ∈ I, Q i ×ˢ ball (c i) r

theorem nearPinPairs_measurable (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) : MeasurableSet (nearPinPairs I Q c r) :=
  Finset.measurableSet_biUnion I (fun i hi => (hQ i hi).prod measurableSet_ball)

omit [BorelSpace Y] in
theorem near_pin_pair_mass (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (K : ℝ≥0∞) (hball : ∀ i ∈ I, ν (ball (c i) r) ≤ K) :
    (μ.prod ν) (nearPinPairs I Q c r) ≤ K*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (Q i ×ˢ ball (c i) r) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, μ (Q i)*ν (ball (c i) r) := by simp only [Measure.prod_prod]
    _ ≤ ∑ i ∈ I, K*μ (Q i) := Finset.sum_le_sum (fun i hi => by
      rw [mul_comm K]
      exact mul_le_mul' le_rfl (hball i hi))
    _ = K*μ (⋃ i ∈ I, Q i) := by rw [← Finset.mul_sum,measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem distance_of_not_nearPinPairs (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    {x : X} {p : Y} (hp : (x,p) ∉ nearPinPairs I Q c r) {i : ι} (hi : i ∈ I)
    (hx : x ∈ Q i) : r ≤ dist p (c i) := by
  by_contra! hdist
  exact hp (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx,hdist⟩⟩)

end Falconer

end OAI
