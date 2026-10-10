import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Gluing.PinnedTest
import OAI.Probability.CriticalPercolation.Gluing.SourceConnectivity
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductEmbedding

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
lemma source_hit_ae_seed (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (G.withSource A).hitEvent none (some '' T) =ᵐ[BernoulliProduct.law q]
      ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,law_coordinate,hq a]
    simp [bitMeasure]
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  exact propext (G.source_hit_iff_seedHit A T ω hω)

lemma source_hit_diff_probability (A B T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹'
        (G.seedHitEvent A B\G.seedHitEvent A T)) := by
    apply measure_congr
    filter_upwards [G.source_hit_ae_seed A B q hq,G.source_hit_ae_seed A T q hq] with ω hB hT
    exact propext (and_congr (eq_iff_iff.mp hB) (not_congr (eq_iff_iff.mp hT)))
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' _)=_
  rw [← Measure.map_apply (Measurable.of_eval (fun bond => measurable_set_mem (Sum.inl bond)))
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) _=_
  rw [law_map_preimage q Sum.inl Sum.inl_injective]
  rfl

lemma restricted_seed_diff_probability (A B T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A B R\G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _)
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  congr 1
  have he (ω : Set E) : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  ext ω
  simp only [Set.mem_sdiff,Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]

lemma restricted_seed_diff_le_source (A B T : Set V) (q : E → unitInterval)
    (I F R σ : Set E) (hFR : F⊆R) :
    (blockProbability q I (G.restrictedSeed A B F\G.restrictedSeed A T R) σ).toReal ≤
      (BernoulliProduct.law (Sum.elim (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)
        (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' B)\(G.withSource A).hitEvent none (some '' T)) := by
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((G.restrictedSeed_measurable _ _ _).diff (G.restrictedSeed_measurable _ _ _))]
  rw [measureReal_def,G.source_hit_diff_probability A B T _ (fun _ => rfl)]
  change (BernoulliProduct.law (pinnedParameters q I σ)).real _ ≤
    (BernoulliProduct.law (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)).real _
  rw [measureReal_def,measureReal_def,← G.restricted_seed_diff_probability]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  exact Set.sdiff_subset_sdiff_left (G.restrictedSeed_mono A B hFR)

end CriticalPercolation.BondGraph
end
end
end

end OAI
