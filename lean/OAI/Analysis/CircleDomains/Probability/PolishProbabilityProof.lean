import OAI.Analysis.CircleDomains.Probability.CompactProbabilityBorel
import OAI.Analysis.CircleDomains.Selection.CompleteEmbeddingGDelta
import OAI.Analysis.CircleDomains.Probability.GDeltaPolish
import OAI.Analysis.CircleDomains.Probability.ProbabilityTopologicalEmbedding
import OAI.Analysis.CircleDomains.Probability.SupportedProbabilityGDelta
import OAI.Analysis.CircleDomains.Probability.PublishedProbabilityTopology

namespace OAI

/-! The weak probability laws on a Polish space are Polish, with the
measure-evaluation Borel structure. Embed the point space in the Hilbert cube;
the laws supported on its G-delta image form a G-delta in the compact law space. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma polishProbabilityLaws (X : Type*) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] : PolishProbabilityLaws X := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX => exact ⟨compact_probability_polish X, compact_probability_borel X⟩
  | inr hX =>
    let : MetricSpace X := metrizableSpaceMetric X
    obtain ⟨f, hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
    have hfm : MeasurableEmbedding f := hf.continuous.measurableEmbedding hf.injective
    let : BorelSpace (ProbabilityMeasure (ℕ → unitInterval)) := compact_probability_borel _
    let : PolishSpace (ProbabilityMeasure (ℕ → unitInterval)) := compact_probability_polish _
    have hF : IsEmbedding (fun μ : ProbabilityMeasure X => μ.map f) :=
      isEmbedding_probability_map hf hfm
    have hr : IsGδ (range (fun μ : ProbabilityMeasure X => μ.map f)) := by
      rw [range_probability_map hfm]
      exact isGDelta_supported_probabilities (isGDelta_range_embedding hf)
    let : PolishSpace (range (fun μ : ProbabilityMeasure X => μ.map f)) :=
      polishSpace_of_isGDelta hr
    have hp : PolishSpace (ProbabilityMeasure X) := hF.toHomeomorph.isClosedEmbedding.polishSpace
    refine ⟨hp, ?_⟩
    have hlo : (inferInstance : MeasurableSpace (ProbabilityMeasure X)) ≤
        borel (ProbabilityMeasure X) := by
      have h : @Measurable (ProbabilityMeasure X) (Measure X)
          (borel (ProbabilityMeasure X)) inferInstance (fun μ => (μ : Measure X)) := by
        let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
        let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
        exact measurable_measure_of_continuous_probability continuous_id
      exact h.comap_le
    have hup : borel (ProbabilityMeasure X) ≤
        (inferInstance : MeasurableSpace (ProbabilityMeasure X)) := by
      rw [hF.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
      exact (measurable_probability_map hfm.measurable).comap_le
    exact ⟨le_antisymm hlo hup⟩

end CircleDomainRigidity

end

end OAI
