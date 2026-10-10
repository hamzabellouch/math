import OAI.Probability.SpanningForest.IntrinsicBridge
import OAI.Probability.SpanningForest.FiniteUSTRelabel

namespace OAI

noncomputable section

namespace Problem336

theorem relabelFiniteSubgraph_inducedCode (σ : Equiv ℕ ℕ) (G : GraphCode)
    (S : Finset ℕ) :
    relabelFiniteSubgraph σ (inducedCode G S) =
      inducedCode (relabelGraph σ G) (S.image σ) := by
  apply Prod.ext
  · rfl
  · ext p
    change p ∈ ((inducedCode G S).2.image (relabelPair σ)) ↔
      p ∈ (inducedCode (relabelGraph σ G) (S.image σ)).2
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      rcases (mem_inducedCode_edges G S q).mp hq with ⟨hu, hv, _, ha⟩
      apply (rawPair_mem_inducedCode_edges (relabelGraph σ G) (S.image σ) _ _).mpr
      exact ⟨Finset.mem_image_of_mem σ hu, Finset.mem_image_of_mem σ hv,
        by simpa [Adj, relabelGraph] using ha⟩
    · intro hp
      rcases (mem_inducedCode_edges (relabelGraph σ G) (S.image σ) p).mp hp with
        ⟨hu, hv, hlt, ha⟩
      have hu' : σ.symm p.1 ∈ S := by
        rcases Finset.mem_image.mp hu with ⟨u, hu, he⟩
        rw [← he]
        simpa using hu
      have hv' : σ.symm p.2 ∈ S := by
        rcases Finset.mem_image.mp hv with ⟨v, hv, he⟩
        rw [← he]
        simpa using hv
      refine Finset.mem_image.mpr ⟨rawPair (σ.symm p.1) (σ.symm p.2), ?_, ?_⟩
      · apply (rawPair_mem_inducedCode_edges G S _ _).mpr
        exact ⟨hu', hv', by simpa [Adj, relabelGraph] using ha⟩
      · simp only [relabelPair_rawPair, Equiv.apply_symm_apply, rawPair_of_lt hlt]

namespace Intrinsic

theorem exhaustion_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    exhaustion (relabelGraph σ G) (mapEdge σ e) n =
      relabelFiniteSubgraph σ (exhaustion G e n) := by
  unfold exhaustion
  rw [edgeBallCode_relabel, relabelFiniteSubgraph_inducedCode]

theorem ustCylinder_exhaustion_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (A B : Finset EdgeCode) :
    ustCylinder (exhaustion (relabelGraph σ G) (mapEdge σ e) n)
      (A.image (mapEdge σ)) (B.image (mapEdge σ)) =
      ustCylinder (exhaustion G e n) A B := by
  rw [exhaustion_relabel]
  apply ustCylinder_relabel
  intro p hp
  exact ((mem_inducedCode_edges G _ p).mp hp).2.2.1

end Intrinsic

namespace IntrinsicExhaustion

theorem edgeBallSubgraph_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (hG : GraphLocallyFinite G) (hσG : GraphLocallyFinite (relabelGraph σ G))
    (e : EdgeCode) (n : ℕ) :
    edgeBallSubgraph (relabelGraph σ G) hσG (mapEdge σ e) n =
      relabelFiniteSubgraph σ (edgeBallSubgraph G hG e n) := by
  rw [← Intrinsic.exhaustion_eq_edgeBallSubgraph (relabelGraph σ G) hσG,
    ← Intrinsic.exhaustion_eq_edgeBallSubgraph G hG, Intrinsic.exhaustion_relabel]

theorem ustCylinder_edgeBallSubgraph_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (hG : GraphLocallyFinite G) (hσG : GraphLocallyFinite (relabelGraph σ G))
    (e : EdgeCode) (n : ℕ) (A B : Finset EdgeCode) :
    ustCylinder (edgeBallSubgraph (relabelGraph σ G) hσG (mapEdge σ e) n)
      (A.image (mapEdge σ)) (B.image (mapEdge σ)) =
      ustCylinder (edgeBallSubgraph G hG e n) A B := by
  rw [← Intrinsic.exhaustion_eq_edgeBallSubgraph (relabelGraph σ G) hσG,
    ← Intrinsic.exhaustion_eq_edgeBallSubgraph G hG]
  exact Intrinsic.ustCylinder_exhaustion_relabel σ G e n A B

end IntrinsicExhaustion
end Problem336

end

end OAI
