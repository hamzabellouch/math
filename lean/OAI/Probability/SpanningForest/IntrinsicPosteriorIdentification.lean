import OAI.Probability.SpanningForest.IntrinsicTreeDrift
import OAI.Probability.SpanningForest.PosteriorTiltLimit
import OAI.Probability.SpanningForest.FiniteUSTIntegrals
import OAI.Probability.SpanningForest.FUSFExistenceReduction

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.GraphTreePosterior

theorem finiteEnergy_finiteTreeConfiguration (T : Finset (ℕ × ℕ))
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    TiltLimit.finiteEnergy S (fun f => y f - t / 2) (finiteTreeConfiguration T) =
      energy T S t y := by
  classical
  unfold TiltLimit.finiteEnergy energy
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : f.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, h]

theorem mean_eq_finiteUSTProbabilityMeasure_tilt (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y =
      TiltLimit.finiteTiltMean (finiteUSTProbabilityMeasure K hK) S
        (fun f => y f - t / 2) e := by
  classical
  unfold TiltLimit.finiteTiltMean TiltLimit.tiltedMean
  change mean K e S t y =
    (∫ X, TiltLimit.bit (X e) *
      Real.exp (TiltLimit.finiteEnergy S (fun f => y f - t / 2) X)
      ∂finiteUSTMeasure K) /
    (∫ X, Real.exp (TiltLimit.finiteEnergy S (fun f => y f - t / 2) X)
      ∂finiteUSTMeasure K)
  rw [integral_ratio_finiteUSTMeasure K hK]
  simp only [finiteEnergy_finiteTreeConfiguration]
  unfold mean numerator partition weight
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : e.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, h]

theorem tendsto_finiteBallMean_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    Tendsto (fun m => finiteBallMean G e n m t y) atTop
      (𝓝 (TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e)) := by
  have hH := Intrinsic.isConnectedExhaustion G hc hf e he
  have hweak := hμ.tendsto_finiteUSTProbabilityMeasure (Intrinsic.exhaustion G e) hH
  have hseq : (fun m => finiteBallMean G e n m t y) =
      (fun m => TiltLimit.finiteTiltMean
        (finiteUSTProbabilityMeasure (Intrinsic.exhaustion G e m)
          (FiniteEncoding.spanningTrees_nonempty (hH.1 m)))
        (edgeCodes (Intrinsic.exhaustion G e n)) (fun f => y f - t / 2) e) := by
    funext m
    exact mean_eq_finiteUSTProbabilityMeasure_tilt _ _ _ _ _ _
  rw [hseq]
  exact TiltLimit.tendsto_finiteTiltMean hweak _ _ _

theorem innerMean_eq_finiteTiltMean_of_hasFUSFLaw
    {G : GraphCode} (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id)
    (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean G e n t y =
      TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e :=
  innerMean_eq_of_tendsto e n t y
    (tendsto_finiteBallMean_of_hasFUSFLaw hc hf hμ e he n t y)

end Problem336.GraphTreePosterior

end

end OAI
