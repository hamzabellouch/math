import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CKSIntrinsicVolume

lemma exists_measure_of_compatible {X ι : Type*} [MeasurableSpace X]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (μ : ι → Measure X)
    (hc : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (f : ℕ → ι) (hf : ⋃ n, U (f n) = univ) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  let D := disjointed (U ∘ f)
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => hU (f n))
  refine ⟨Measure.sum (fun n => (μ (f n)).restrict (D n)), fun i => ?_⟩
  rw [Measure.restrict_sum _ (hU i)]
  have heq : ∀ n, ((μ (f n)).restrict (D n)).restrict (U i) = (μ i).restrict (D n) := by
    intro n
    rw [Measure.restrict_comm (hU i), hc (f n) i]
    exact Measure.restrict_restrict_of_subset (disjointed_subset (U ∘ f) n)
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed (U ∘ f)) hD,
    show (⋃ n, D n) = univ from (iUnion_disjointed.trans hf), Measure.restrict_univ]

end CKSIntrinsicVolume

end

end OAI
