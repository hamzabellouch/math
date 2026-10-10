import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_measure_prod_sum {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : Finset ι) (T : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    (∑ i ∈ S, μ i).prod (∑ j ∈ T, ν j) = ∑ i ∈ S, ∑ j ∈ T, (μ i).prod (ν j) := by
  apply Measure.ext_prod
  intro s t hs ht
  simp only [Measure.prod_prod,Measure.finsetSum_apply,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem finite_measure_restrict_sum {α ι : Type*} [MeasurableSpace α]
    (S : Finset ι) (μ : ι → Measure α) (A : Set α) :
    (∑ i ∈ S, μ i).restrict A = ∑ i ∈ S, (μ i).restrict A := by
  ext s hs
  simp only [Measure.restrict_apply hs,Measure.finsetSum_apply]

end PlanarFalconer

end OAI
