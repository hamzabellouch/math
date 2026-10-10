import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Measure

lemma tprod_ac {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,SigmaFinite (μ i)] [∀i,SigmaFinite (ν i)]
    (h : ∀i,μ i ≪ ν i) (l : List ι) : Measure.tprod l μ ≪ Measure.tprod l ν := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [Measure.tprod_cons, Measure.tprod_cons]
    exact (h i).prod ih

lemma pi_ac {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,SigmaFinite (μ i)] [∀i,SigmaFinite (ν i)]
    (h : ∀i,μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  classical
  let : Encodable ι := Fintype.toEncodable ι
  rw [←Measure.pi'_eq_pi μ,←Measure.pi'_eq_pi ν,Measure.pi',Measure.pi']
  simpa only [MeasurableEquiv.piMeasurableEquivTProd_symm_apply] using
    (MeasurableEquiv.piMeasurableEquivTProd (Encodable.sortedUniv_nodup ι) (Encodable.mem_sortedUniv)).symm.measurableEmbedding.absolutelyContinuous_map
      (tprod_ac μ ν h (Encodable.sortedUniv ι))

lemma ac_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ ν : Measure X}
    {f : X→Y} (hf : Measurable f) (h : μ ≪ ν) : μ.map f ≪ ν.map f := by
  refine Measure.AbsolutelyContinuous.mk fun S hS hnull ↦ ?_
  rw [Measure.map_apply hf hS] at hnull ⊢
  exact h hnull

end HardSphere.Measure

end
end

end

end OAI
