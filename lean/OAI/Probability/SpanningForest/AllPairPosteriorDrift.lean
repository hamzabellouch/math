import OAI.Probability.SpanningForest.AllPairIntrinsicBridge
import OAI.Probability.SpanningForest.IntrinsicPosteriorDrift
import OAI.Probability.SpanningForest.PosteriorNullCoordinates

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.GraphTreePosterior

theorem finiteTiltMean_eq_allPair_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (n : ℕ) (h : EdgeCode → ℝ) (a : EdgeCode) :
    TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n)) h a =
      TiltLimit.finiteTiltMean μ (AllPairObservation.observations G e n) h a := by
  apply TiltLimit.finiteTiltMean_eq_of_zero_extra μ
    (AllPairObservation.edgeCodes_exhaustion_subset_observations hf e n)
  obtain ⟨H, hH⟩ := hc.exists_connected_exhaustion
  filter_upwards [hμ.ae_subgraph H hH] with X hX
  intro f hT hS
  cases hxf : X f with
  | false => rfl
  | true =>
      exact False.elim
        (AllPairObservation.not_adj_of_mem_observations_not_mem_edgeCodes hf e f n hT hS
          (hX f hxf))

theorem drift_eq_allPair_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    drift G t y e =
      PosteriorDrift.drift μ (AllPairObservation.observations G) t y e := by
  rw [drift_eq_posteriorDrift_all_of_hasFUSFLaw hc hf hμ]
  change Filter.limsup
      (fun n => TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e) Filter.atTop =
    Filter.limsup
      (fun n => TiltLimit.finiteTiltMean μ (AllPairObservation.observations G e n)
        (fun f => y f - t / 2) e) Filter.atTop
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall fun n =>
    finiteTiltMean_eq_allPair_of_hasFUSFLaw hc hf hμ e n (fun f => y f - t / 2) e

theorem drift_fun_eq_allPair_posteriorDrift_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id) :
    drift G = PosteriorDrift.drift μ (AllPairObservation.observations G) := by
  funext t y e
  exact drift_eq_allPair_posteriorDrift_of_hasFUSFLaw hc hf hμ e t y

end Problem336.GraphTreePosterior

end

end OAI
