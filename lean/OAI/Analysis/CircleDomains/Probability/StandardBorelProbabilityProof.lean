import OAI.Analysis.CircleDomains.Probability.CompactProbabilityBorel
import OAI.Analysis.CircleDomains.Probability.ProbabilityMeasureEmbedding
import OAI.Analysis.CircleDomains.Probability.StandardBorelEmbedding
import OAI.Analysis.CircleDomains.Probability.PublishedProbabilityTopology

namespace OAI

/-! Probability laws on a standard Borel space are standard Borel.
Embed the point space into Cantor space and identify the image of the
induced map on laws by its measurable support condition. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma standardBorelProbabilityLaws (A : Type*) [MeasurableSpace A] [StandardBorelSpace A] :
    StandardBorelProbabilityLaws A := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    have : IsEmpty (ProbabilityMeasure A) := ⟨fun μ => by
      have hm : (μ : Measure A) univ = 1 := measure_univ
      have hu : (univ : Set A) = ∅ := Set.eq_empty_of_isEmpty _
      rw [hu, measure_empty] at hm
      exact zero_ne_one hm⟩
    change StandardBorelSpace (ProbabilityMeasure A)
    infer_instance
  | inr hA =>
    obtain ⟨f, hfm, hfi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated A
    have hf : MeasurableEmbedding f := hfm.measurableEmbedding hfi
    let : BorelSpace (ProbabilityMeasure (ℕ → Bool)) := compact_probability_borel _
    let : PolishSpace (ProbabilityMeasure (ℕ → Bool)) := compact_probability_polish _
    exact standardBorel_of_measurableEmbedding (measurableEmbedding_probability_map hf)

end CircleDomainRigidity

end

end OAI
