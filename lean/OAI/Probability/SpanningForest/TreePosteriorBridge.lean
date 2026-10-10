import OAI.Probability.SpanningForest.IntrinsicTreeDrift
import OAI.Probability.SpanningForest.USTPosteriorResponse

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.GraphTreePosterior

theorem energy_eq_finiteEnergy (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    energy T S t y =
      TiltLimit.finiteEnergy S (fun f => y f - t / 2) (finiteTreeConfiguration T) := by
  classical
  simp only [energy, TiltLimit.finiteEnergy, USTResponse.bit_finiteTreeConfiguration,
    mul_ite, mul_one, mul_zero]

theorem mean_eq_finiteTiltMean (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y =
      TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S (fun f => y f - t / 2) e := by
  classical
  rw [TiltLimit.finiteTiltMean, USTResponse.tiltedMean_finiteUSTProbability]
  simp_rw [← energy_eq_finiteEnergy]
  change numerator K e S t y / partition K S t y =
    (∑ T : USTResponse.TreeSample K,
      TiltLimit.bit (finiteTreeConfiguration T.1 e) * weight T.1 S t y) /
    (∑ T : USTResponse.TreeSample K, weight T.1 S t y)
  congr 1
  · rw [← Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
      (fun T => TiltLimit.bit (finiteTreeConfiguration T e) * weight T S t y)]
    simp only [numerator, USTResponse.bit_finiteTreeConfiguration,
      ite_mul, one_mul, zero_mul, Finset.sum_filter]
  · exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl) (fun T => weight T S t y)

theorem mean_eq_finiteTilt (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y = USTResponse.finiteTilt K (S.image Subtype.val) 0
      (USTResponse.extendMarks (fun f => y f - t / 2)) e.1 := by
  rw [mean_eq_finiteTiltMean K hne, USTResponse.finiteTiltMean_eq_finiteTilt]

theorem mean_response_of_inclusion_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hresponse : ∀ (a b : USTResponse.FiniteEdge K → ℝ)
      (e : USTResponse.FiniteEdge K) (D : ℝ),
      0 ≤ D → (∀ f, |b f - a f| ≤ D) →
        |USTResponse.inclusion K b e - USTResponse.inclusion K a e| ≤ D / 2)
    (e : EdgeCode) (S : Finset EdgeCode) (t : ℝ) (y z : EdgeCode → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hyz : ∀ f ∈ S, |y f - z f| ≤ D) :
    |mean K e S t y - mean K e S t z| ≤ D / 2 := by
  rw [mean_eq_finiteTiltMean K hne, mean_eq_finiteTiltMean K hne]
  apply USTResponse.finiteUST_posterior_response_of_response K hne hresponse S
    (fun f => z f - t / 2) (fun f => y f - t / 2) e D hD
  intro f hf
  simpa only [sub_sub_sub_cancel_right] using hyz f hf

theorem innerMean_eq_posterior_of_weak_limit (G : GraphCode) (e : EdgeCode)
    (hne : ∀ m, (spanningTrees (Intrinsic.exhaustion G e m)).Nonempty)
    (μ : ProbabilityMeasure EdgeConfiguration)
    (hμ : Tendsto (fun m => finiteUSTProbability (Intrinsic.exhaustion G e m) (hne m))
      atTop (nhds μ)) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean G e n t y =
      TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e := by
  apply innerMean_eq_of_tendsto
  have h := TiltLimit.tendsto_finiteTiltMean hμ
    (edgeCodes (Intrinsic.exhaustion G e n)) (fun f => y f - t / 2) e
  simpa only [finiteBallMean, mean_eq_finiteTiltMean _ (hne _)] using h

end Problem336.GraphTreePosterior

end

end OAI
