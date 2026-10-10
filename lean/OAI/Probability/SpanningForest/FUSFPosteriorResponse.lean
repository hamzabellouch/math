import OAI.Probability.SpanningForest.CodedMarginal
import OAI.Probability.SpanningForest.USTPosteriorResponse
import OAI.Probability.SpanningForest.FUSFExistenceReduction
import OAI.Probability.SpanningForest.ExhaustionExistence
import OAI.Probability.SpanningForest.PosteriorDrift

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336

theorem HasFUSFLaw.finiteTiltMean_response
    {G : GraphCode} (hc : GraphConnected G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h f - h' f| ≤ D) :
    |TiltLimit.finiteTiltMean μ S h e - TiltLimit.finiteTiltMean μ S h' e| ≤ D / 2 := by
  obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
  apply TiltLimit.finiteTiltMean_response_bound_of_tendsto
    (hμ.tendsto_finiteUSTProbabilityMeasure H hH) S h h' e
  apply Filter.Eventually.of_forall
  intro n
  exact USTResponse.finiteUST_posterior_response_of_response (H n)
    (FiniteEncoding.spanningTrees_nonempty (hH.1 n))
    (USTResponse.inclusion_response_connected (hH.1 n)) S h' h e D hD hh

theorem HasFUSFLaw.finiteResponseBound
    {G : GraphCode} (hc : GraphConnected G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (S : EdgeCode → ℕ → Finset EdgeCode) :
    PosteriorDrift.FiniteResponseBound μ S (1 / 2 : ℝ) := by
  intro e n h h' D hD hh
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    hμ.finiteTiltMean_response hc (S e n) h h' e D hD hh

end Problem336

end

end OAI
