import OAI.Probability.SpanningForest.FiniteUSTLimit
import OAI.Probability.SpanningForest.GraphEncoding

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

theorem exists_hasFUSFLaw_of_inclusion_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A, Tendsto (fun n => ustCylinder (H' n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id :=
  exists_hasFUSFLaw_of_common_inclusion_limits G H hH
    (fun _ hH' n => FiniteEncoding.spanningTrees_nonempty (hH'.1 n)) L hL

theorem HasFUSFLaw.tendsto_finiteUSTProbabilityMeasure
    {G : GraphCode} {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H) :
    Tendsto (fun n => finiteUSTProbabilityMeasure (H n)
      (FiniteEncoding.spanningTrees_nonempty (hH.1 n))) atTop (𝓝 μ) := by
  apply BinaryLaw.tendsto_iff_signedCylinders.mpr
  intro A B
  change Tendsto (fun n => finiteUSTMeasure (H n) (edgeCylinder A B)) atTop
    (𝓝 ((μ : Measure EdgeConfiguration) (edgeCylinder A B)))
  simp only [finiteUSTMeasure_edgeCylinder]
  exact hμ.2 H hH A B

end Problem336

end

end OAI
