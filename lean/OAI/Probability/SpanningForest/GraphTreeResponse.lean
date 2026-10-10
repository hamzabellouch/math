import OAI.Probability.SpanningForest.TreePosteriorBridge
import OAI.Probability.SpanningForest.GraphEncoding

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336

theorem Intrinsic.exhaustion_spanningTrees_nonempty (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.1.1 e.1.2) (n : ℕ) :
    (spanningTrees (Intrinsic.exhaustion G e n)).Nonempty :=
  FiniteEncoding.spanningTrees_nonempty (Intrinsic.exhaustion_finiteConnected G hG e he n)

namespace GraphTreePosterior

theorem finiteBallMean_response_of_connected_response (G : GraphCode)
    (hG : GraphLocallyFinite G)
    (hresponse : ∀ (K : FiniteSubgraphCode), IsFiniteConnectedSubgraph G K →
      ∀ (a b : USTResponse.FiniteEdge K → ℝ)
        (e : USTResponse.FiniteEdge K) (D : ℝ),
        0 ≤ D → (∀ f, |b f - a f| ≤ D) →
          |USTResponse.inclusion K b e - USTResponse.inclusion K a e| ≤ D / 2)
    (e : EdgeCode) (n m : ℕ) (t : ℝ) (y z : EdgeCode → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hyz : ∀ f ∈ edgeCodes (Intrinsic.exhaustion G e n), |y f - z f| ≤ D) :
    |finiteBallMean G e n m t y - finiteBallMean G e n m t z| ≤ D / 2 := by
  by_cases he : Adj G e.1.1 e.1.2
  · exact mean_response_of_inclusion_response (Intrinsic.exhaustion G e m)
      (Intrinsic.exhaustion_spanningTrees_nonempty G hG e he m)
      (hresponse _ (Intrinsic.exhaustion_finiteConnected G hG e he m))
      e (edgeCodes (Intrinsic.exhaustion G e n)) t y z D hD hyz
  · simp only [finiteBallMean_of_not_adj e he, sub_self, abs_zero]
    exact div_nonneg hD (by norm_num)

theorem drift_response_of_connected_response (G : GraphCode)
    (hG : GraphLocallyFinite G)
    (hresponse : ∀ (K : FiniteSubgraphCode), IsFiniteConnectedSubgraph G K →
      ∀ (a b : USTResponse.FiniteEdge K → ℝ)
        (e : USTResponse.FiniteEdge K) (D : ℝ),
        0 ≤ D → (∀ f, |b f - a f| ≤ D) →
          |USTResponse.inclusion K b e - USTResponse.inclusion K a e| ≤ D / 2)
    (t : ℝ) (y z : EdgeCode → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hyz : ∀ f, Adj G f.1.1 f.1.2 → |y f - z f| ≤ D) (e : EdgeCode) :
    |drift G t y e - drift G t z e| ≤ D / 2 := by
  apply drift_response_of_finite e t y z
  intro n m
  apply finiteBallMean_response_of_connected_response G hG hresponse e n m t y z D hD
  intro f hf
  apply hyz f
  exact ((mem_inducedCode_edges G (edgeBallCode G n e) f.1).mp
    ((mem_edgeCodes (Intrinsic.exhaustion G e n) f).mp hf)).2.2.2

theorem innerMean_eq_posterior_of_graph_weak_limit (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (μ : ProbabilityMeasure EdgeConfiguration)
    (hμ : Tendsto (fun m => finiteUSTProbability (Intrinsic.exhaustion G e m)
      (Intrinsic.exhaustion_spanningTrees_nonempty G hG e he m)) atTop (nhds μ))
    (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean G e n t y =
      TiltLimit.finiteTiltMean μ (edgeCodes (Intrinsic.exhaustion G e n))
        (fun f => y f - t / 2) e :=
  innerMean_eq_posterior_of_weak_limit G e
    (Intrinsic.exhaustion_spanningTrees_nonempty G hG e he) μ hμ n t y

end GraphTreePosterior
end Problem336

end

end OAI
