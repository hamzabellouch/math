import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

abbrev coordinateSigma (e : E) : MeasurableSpace (Set E) :=
  MeasurableSpace.comap (fun ω : Set E => e ∈ ω) inferInstance

abbrev blockSigma (S : Set E) : MeasurableSpace (Set E) := ⨆ e ∈ S, coordinateSigma e

lemma coordinateSigma_le (e : E) : coordinateSigma e ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  (measurable_set_mem e).comap_le

lemma blockSigma_le (S : Set E) : blockSigma S ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  iSup₂_le fun e _ => coordinateSigma_le e

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

def forceOn (S : Set E) (σ ω : Set E) : Set E := fun e => if e ∈ S then e ∈ σ else e ∈ ω

lemma measurable_forceOn_block (S σ : Set E) :
    @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance (forceOn S σ) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop) (blockSigma Sᶜ)
    (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e ∈ S
  · simpa only [forceOn, ite_eq_left he] using
      (@measurable_const Prop (Set E) inferInstance (blockSigma Sᶜ) (e ∈ σ))
  · have hm : @Measurable (Set E) Prop (coordinateSigma e) inferInstance
        (fun ω => e ∈ ω) := measurable_iff_comap_le.mpr le_rfl
    have hl : coordinateSigma e ≤ blockSigma Sᶜ := le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn, ite_eq_right he] using hm.mono hl le_rfl

lemma measurable_forceOn (S σ : Set E) : Measurable (forceOn S σ) :=
  (measurable_forceOn_block S σ).mono (blockSigma_le Sᶜ) le_rfl

theorem zero_one_of_finite_erasure_invariant (q : E → unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinvariant : ∀ (S : Set E), S.Finite → ∀ ω,
      forceOn S ∅ ω ∈ A ↔ ω ∈ A) : law q A = 0 ∨ law q A = 1 := by
  let mA : MeasurableSpace (Set E) := MeasurableSpace.generateFrom {A}
  have hmA : mA ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) := MeasurableSpace.generateFrom_singleton_le hA
  have hi : ∀ S : Finset E, Indep (blockSigma (S : Set E)) mA (law q) := by
    intro S
    have htail : MeasurableSet[blockSigma (S : Set E)ᶜ] A := by
      have hh := hA.preimage (measurable_forceOn_block (S : Set E) ∅)
      have heq : forceOn (S : Set E) ∅ ⁻¹' A = A := by
        ext ω
        exact hinvariant _ S.finite_toSet ω
      rwa [heq] at hh
    exact indep_of_indep_of_le_right (independent_blocks q (S : Set E))
      (MeasurableSpace.generateFrom_singleton_le htail)
  have hd : Directed (· ≤ ·) (fun S : Finset E => blockSigma (S : Set E)) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩ <;> apply iSup₂_le <;> intro e he
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_left T he) le_rfl)
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_right S he) le_rfl)
  have hall : (⨆ S : Finset E, blockSigma (S : Set E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
    apply le_antisymm (iSup_le fun S => blockSigma_le _)
    change (⨆ e, coordinateSigma e) ≤ _
    apply iSup_le
    intro e
    exact le_iSup_of_le {e} (le_iSup_of_le e
      (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl))
  have h := indep_iSup_of_directed_le hi (fun S => blockSigma_le (S : Set E)) hmA hd
  rw [hall] at h
  exact measure_eq_zero_or_one_of_indepSet_self
    (h.indepSet_of_measurableSet hA (MeasurableSpace.measurableSet_generateFrom (by simp)))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
