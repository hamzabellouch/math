import OAI.Probability.SpanningForest.TotalTreeResponse
import OAI.Probability.SpanningForest.CodedMarginal

namespace OAI

noncomputable section

namespace Problem336.GraphTreePosterior

theorem mean_response_connected {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y z : EdgeCode → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hyz : ∀ f ∈ S, |y f - z f| ≤ D) :
    |mean K e S t y - mean K e S t z| ≤ D / 2 :=
  mean_response_of_inclusion_response K (FiniteEncoding.spanningTrees_nonempty hK)
    (USTResponse.inclusion_response_connected hK) e S t y z D hD hyz

theorem finiteBallMean_response (G : GraphCode) (e : EdgeCode) (n m : ℕ)
    (t : ℝ) (y z : EdgeCode → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hyz : ∀ f ∈ edgeCodes (Intrinsic.exhaustion G e n), |y f - z f| ≤ D) :
    |finiteBallMean G e n m t y - finiteBallMean G e n m t z| ≤ D / 2 :=
  finiteBallMean_response_total G
    (fun _ hK => USTResponse.inclusion_response_connected hK) e n m t y z D hD hyz

theorem drift_response (G : GraphCode) (t : ℝ) (y z : EdgeCode → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hyz : ∀ f, Adj G f.1.1 f.1.2 → |y f - z f| ≤ D) (e : EdgeCode) :
    |drift G t y e - drift G t z e| ≤ D / 2 :=
  drift_response_total G
    (fun _ hK => USTResponse.inclusion_response_connected hK) t y z D hD hyz e

theorem drift_picard_response (G : GraphCode) (t : ℝ) (y z : EdgeCode → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hyz : ∀ f, |y f - z f| ≤ D) (e : EdgeCode) :
    |drift G t y e - drift G t z e| ≤ (1 / 2 : ℝ) * D := by
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    drift_response G t y z D hD (fun f _ => hyz f) e

end Problem336.GraphTreePosterior

end

end OAI
