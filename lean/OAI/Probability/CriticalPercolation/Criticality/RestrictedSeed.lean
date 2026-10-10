import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.PredictionFailure
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def restrictedSeed (A T : Set V) (S : Set E) : Set (Set E) :=
  {ω | ω∩S∈G.seedHitEvent A T}

lemma restrictedSeed_mono (A T : Set V) {S U : Set E} (h : S⊆U) :
    G.restrictedSeed A T S⊆G.restrictedSeed A T U := by
  intro ω hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_right _ h) hω

lemma measurableSet_restrictedSeed [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet[blockSigma S] (G.restrictedSeed A T S) :=
  (G.measurableSet_seedHitEvent A T).preimage (measurable_inter_block S)

lemma restrictedSeed_measurable [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet (G.restrictedSeed A T S) :=
  (blockSigma_le S) _ (G.measurableSet_restrictedSeed A T S)

lemma seed_prediction_persists [Countable V] [Countable E]
    (q : E → unitInterval) (A T : Set V) (I F D σ : Set E)
    (hIF : I⊆F) (hfresh : F∩D⊆I) :
    blockProbability q I (G.restrictedSeed A T (I∪D)) σ ≤
      blockProbability q F (G.restrictedSeed A T (F∪D)) σ := by
  have hrestrict : I∩(I∪D)=F∩(I∪D) := by
    ext e
    constructor <;> intro h
    · exact ⟨hIF h.1,h.2⟩
    · rcases h.2 with hi|hd
      · exact ⟨hi,Or.inl hi⟩
      · exact ⟨hfresh ⟨h.1,hd⟩,Or.inr hd⟩
  rw [prediction_persists q I F (I∪D) σ σ _
    (G.measurableSet_restrictedSeed A T (I∪D)) hrestrict (fun _ _ => Iff.rfl)]
  apply measure_mono
  intro ω hω
  exact G.restrictedSeed_mono A T (Set.union_subset_union_left D hIF) hω

lemma restrictedSeed_self (A T : Set V) (h : (A∩T).Nonempty) (S : Set E) :
    G.restrictedSeed A T S=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  obtain ⟨v,hvA,hvT⟩ := h
  exact Set.mem_iUnion₂.mpr ⟨v,hvA,v,SimpleGraph.Reachable.refl _,hvT⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
