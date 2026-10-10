import OAI.Probability.SpanningForest.GraphTreeResponse

namespace OAI

noncomputable section

namespace Problem336
namespace Intrinsic

theorem exhaustion_finiteConnected_of_finite (G : GraphCode) (e : EdgeCode)
    (he : Adj G e.1.1 e.1.2) (n : ℕ) (hf : (Problem336.edgeBall G n e).Finite) :
    IsFiniteConnectedSubgraph G (exhaustion G e n) := by
  have hm (v : ℕ) : v ∈ (exhaustion G e n).1 ↔ v ∈ Problem336.edgeBall G n e := by
    simp [exhaustion, edgeBallCode, finiteSetCode, hf]
  have ha (u v : ℕ) : SubgraphAdj (exhaustion G e n) u v ↔
      u ∈ Problem336.edgeBall G n e ∧ v ∈ Problem336.edgeBall G n e ∧ Adj G u v := by
    simp [exhaustion, subgraphAdj_inducedCode, edgeBallCode, finiteSetCode, hf]
  have hpath (v : ℕ) (hv : v ∈ (exhaustion G e n).1) :
      Relation.ReflTransGen (SubgraphAdj (exhaustion G e n)) e.1.1 v := by
    have hv' : v ∈ IntrinsicExhaustion.edgeBall G e n := by
      rw [← edgeBall_eq_selected]
      exact (hm v).mp hv
    apply Relation.ReflTransGen.mono _ _ _ (IntrinsicExhaustion.edgeBall_reachable he hv')
    intro u w huw
    apply (ha u w).mpr
    simpa only [edgeBall_eq_selected] using huw
  refine ⟨⟨e.1.1, (hm _).mpr (Or.inl (withinRadius_refl G n _))⟩, ?_, ?_⟩
  · intro p hp
    exact (mem_inducedCode_edges G _ p).mp hp
  · intro u hu v hv
    let : Std.Symm (SubgraphAdj (exhaustion G e n)) := ⟨fun x y hxy => by
      obtain ⟨hx, hy, hadj⟩ := (ha x y).mp hxy
      exact (ha y x).mpr ⟨hy, hx, (G.2.2 y x).trans hadj⟩⟩
    exact (symm (hpath u hu)).trans (hpath v hv)

theorem exhaustion_eq_empty_of_not_finite (G : GraphCode) (e : EdgeCode) (n : ℕ)
    (hf : ¬ (Problem336.edgeBall G n e).Finite) :
    exhaustion G e n = (∅, ∅) := by
  simp [exhaustion, edgeBallCode, finiteSetCode, hf, inducedCode]

end Intrinsic

namespace GraphTreePosterior

theorem mean_empty (e : EdgeCode) (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean (∅, ∅) e S t y = 0 := by
  classical
  have htrees : spanningTrees (∅, ∅) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro tree _ htree
    have hcard : tree.card + 1 = 0 := htree.2.1
    omega
  simp [mean, numerator, partition, htrees]

theorem finiteBallMean_response_total (G : GraphCode)
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
  · by_cases hf : (Problem336.edgeBall G m e).Finite
    · have hK := Intrinsic.exhaustion_finiteConnected_of_finite G e he m hf
      exact mean_response_of_inclusion_response (Intrinsic.exhaustion G e m)
        (FiniteEncoding.spanningTrees_nonempty hK) (hresponse _ hK)
        e (edgeCodes (Intrinsic.exhaustion G e n)) t y z D hD hyz
    · simp only [finiteBallMean, Intrinsic.exhaustion_eq_empty_of_not_finite G e m hf,
        mean_empty, sub_self, abs_zero]
      exact div_nonneg hD (by norm_num)
  · simp only [finiteBallMean_of_not_adj e he, sub_self, abs_zero]
    exact div_nonneg hD (by norm_num)

theorem drift_response_total (G : GraphCode)
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
  apply finiteBallMean_response_total G hresponse e n m t y z D hD
  intro f hf
  apply hyz f
  exact ((mem_inducedCode_edges G (edgeBallCode G n e) f.1).mp
    ((mem_edgeCodes (Intrinsic.exhaustion G e n) f).mp hf)).2.2.2

end GraphTreePosterior
end Problem336

end

end OAI
