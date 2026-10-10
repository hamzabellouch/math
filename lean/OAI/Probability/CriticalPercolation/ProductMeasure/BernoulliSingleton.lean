import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma force_singleton_inter (q : E → unitInterval) (e : E) (σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    law q (A ∩ {ω : Set E | (e∈ω)=(e∈σ)}) =
      bitMeasure (q e) {e∈σ} * law q (forceOn {e} σ ⁻¹' A) := by
  let C := {ω : Set E | (e∈ω)=(e∈σ)}
  let B := forceOn {e} σ ⁻¹' A
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e∈σ},MeasurableSet.singleton _,rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e≤blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have heq : A∩C = C∩B := by
    ext ω
    have hf (hω : ω∈C) : forceOn {e} σ ω=ω := by
      ext f
      by_cases he : f=e
      · subst f
        simpa only [mem_forceOn,Set.mem_singleton_iff,ite_true] using Iff.of_eq hω.symm
      · simp only [mem_forceOn,Set.mem_singleton_iff,ite_eq_right he]
    constructor
    · rintro ⟨ha,hc⟩
      exact ⟨hc,by change forceOn {e} σ ω∈A; rwa [hf hc]⟩
    · rintro ⟨hc,hb⟩
      exact ⟨by change forceOn {e} σ ω∈A at hb; rwa [hf hc] at hb,hc⟩
  change law q (A∩C)=_
  rw [heq,hmul]
  change law q {ω : Set E | (e∈ω)=(e∈σ)} * _ = _
  rw [law_coordinate]

lemma law_singleton_decomposition (q : E → unitInterval) (e : E) :
    law q = bitMeasure (q e) {True} • (law q).map (forceOn {e} Set.univ) +
      bitMeasure (q e) {False} • (law q).map (forceOn {e} ∅) := by
  ext A hA
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    Measure.map_apply (measurable_forceOn _ _) hA,
    Measure.map_apply (measurable_forceOn _ _) hA]
  simp only [smul_eq_mul]
  have ht := force_singleton_inter q e Set.univ A hA
  have hf := force_singleton_inter q e ∅ A hA
  simp only [Set.mem_univ,Set.mem_empty_iff_false] at ht hf
  rw [←ht,←hf]
  have he : {ω : Set E | (e∈ω)=False} = {ω : Set E | (e∈ω)=True}ᶜ := by
    ext ω
    simp
  rw [he,←Set.sdiff_eq]
  exact (measure_inter_add_sdiff A (measurableSet_eq_fun (measurable_set_mem e) measurable_const)).symm

end CriticalPercolation.BernoulliProduct
end
end

end OAI
