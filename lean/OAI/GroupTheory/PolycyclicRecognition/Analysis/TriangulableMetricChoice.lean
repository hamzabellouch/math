import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangulableLieModel

namespace OAI

/-! # Choosing the endpoint metrics after the topological model reduction -/

noncomputable section
namespace PolycyclicRecognition

/-- The topological model can be fixed before either endpoint metric.
This permits selecting a minimizing-path metric on the Lie model while
retaining the comparison through the two locally compact intermediate groups. -/
theorem exists_realTriangulable_model_with_metric_choice
    (ct : CornulierTesseraModelInput) (metricInput : GeodesicMetricExistenceInput)
    (S : SimplyConnectedSolvableLieModel) :
    ∃ T : SimplyConnectedSolvableLieModel, IsRealTriangulable T ∧
      ∀ (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier),
        letI := dS.compatibleMetric
        letI := dT.compatibleMetric
        Nonempty (MetricQuasiEquivalence S.carrier T.carrier) := by
  obtain ⟨T, hT, G₁, G₂, ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ := ct S
  obtain ⟨d₁⟩ := metricInput G₁.carrier G₁.compactlyGenerated
  obtain ⟨d₂⟩ := metricInput G₂.carrier G₂.compactlyGenerated
  refine ⟨T, hT, ?_⟩
  intro dS dT
  let := dS.compatibleMetric
  let := dT.compatibleMetric
  let := d₁.compatibleMetric
  let := d₂.compatibleMetric
  obtain ⟨e₁⟩ := f₁.nonempty_metricQuasiEquivalence d₁ dS
  obtain ⟨e₂⟩ := f₂.nonempty_metricQuasiEquivalence d₁ d₂
  obtain ⟨e₃⟩ := f₃.nonempty_metricQuasiEquivalence dT d₂
  exact ⟨(e₁.symm.trans e₂).trans e₃.symm⟩

end PolycyclicRecognition

end

end OAI
