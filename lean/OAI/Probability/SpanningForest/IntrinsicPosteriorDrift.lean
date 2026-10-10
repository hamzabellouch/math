import OAI.Probability.SpanningForest.IntrinsicPosteriorIdentification
import OAI.Probability.SpanningForest.PosteriorSupport
import OAI.Probability.SpanningForest.FUSFLawSupport
import OAI.Probability.SpanningForest.ExhaustionExistence

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.GraphTreePosterior

theorem drift_eq_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (fun f n => edgeCodes (Intrinsic.exhaustion G f n)) t y e := by
  unfold drift PosteriorDrift.drift
  congr 1
  funext n q
  exact innerMean_eq_finiteTiltMean_of_hasFUSFLaw hc hf hμ e he n q.1 q.2

theorem drift_eq_posteriorDrift_all_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (fun f n => edgeCodes (Intrinsic.exhaustion G f n)) t y e := by
  by_cases he : Adj G e.1.1 e.1.2
  · exact drift_eq_posteriorDrift_of_hasFUSFLaw hc hf hμ e he t y
  · obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
    have habsent : ∀ᵐ X ∂(μ : Measure EdgeConfiguration), X e = false :=
      hμ.ae_false_of_nonedge H hH e he
    rw [drift_of_not_adj e he t y,
      PosteriorDrift.drift_eq_zero_of_ae_absent μ _ t y e habsent]

end Problem336.GraphTreePosterior

end

end OAI
