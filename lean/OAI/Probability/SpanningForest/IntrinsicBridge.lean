import OAI.Probability.SpanningForest.GraphBalls
import OAI.Probability.SpanningForest.InducedCode
import OAI.Probability.SpanningForest.IntrinsicExhaustion

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.Intrinsic

theorem withinRadius_iff_vertexBall (G : GraphCode) (n u v : ℕ) :
    withinRadius G n u v ↔ v ∈ IntrinsicExhaustion.vertexBall G u n := by
  induction n generalizing v with
  | zero => simp [withinRadius, IntrinsicExhaustion.vertexBall, eq_comm]
  | succ n ih =>
      simp only [withinRadius, IntrinsicExhaustion.mem_vertexBall_succ, ih]

theorem edgeBall_eq_selected (G : GraphCode) (e : EdgeCode) (n : ℕ) :
    Problem336.edgeBall G n e = IntrinsicExhaustion.edgeBall G e n := by
  ext v
  simp only [Problem336.edgeBall, IntrinsicExhaustion.edgeBall,
    Set.mem_ofPred_eq, Set.mem_union, withinRadius_iff_vertexBall]

def exhaustion (G : GraphCode) (e : EdgeCode) (n : ℕ) : FiniteSubgraphCode :=
  inducedCode G (edgeBallCode G n e)

theorem measurable_exhaustion :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => exhaustion q.1 q.2.2 q.2.1) := by
  exact measurable_inducedCode measurable_fst measurable_edgeBallCode

theorem exhaustion_eq_edgeBallSubgraph (G : GraphCode) (hf : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) :
    exhaustion G e n = IntrinsicExhaustion.edgeBallSubgraph G hf e n := by
  apply Prod.ext
  · ext v
    simp only [exhaustion, inducedCode_vertices, mem_edgeBallCode G hf,
      IntrinsicExhaustion.mem_edgeBallSubgraph_vertices, edgeBall_eq_selected]
  · ext p
    simp only [exhaustion, mem_inducedCode_edges, mem_edgeBallCode G hf,
      IntrinsicExhaustion.mem_edgeBallSubgraph_edges, edgeBall_eq_selected]

@[simp] theorem subgraphAdj_exhaustion (G : GraphCode) (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n u v : ℕ) :
    SubgraphAdj (exhaustion G e n) u v ↔
      u ∈ Problem336.edgeBall G n e ∧ v ∈ Problem336.edgeBall G n e ∧ Adj G u v := by
  simp only [exhaustion, subgraphAdj_inducedCode, mem_edgeBallCode G hG]

theorem exhaustion_finiteConnected (G : GraphCode) (hG : GraphLocallyFinite G)
    (e : EdgeCode) (he : Adj G e.val.1 e.val.2) (n : ℕ) :
    IsFiniteConnectedSubgraph G (exhaustion G e n) := by
  rw [exhaustion_eq_edgeBallSubgraph G hG]
  exact IntrinsicExhaustion.isFiniteConnectedSubgraph_edgeBallSubgraph hG e he n

theorem exhaustion_mono (G : GraphCode) (hG : GraphLocallyFinite G)
    (e : EdgeCode) {n m : ℕ} (hnm : n ≤ m) :
    (exhaustion G e n).1 ⊆ (exhaustion G e m).1 ∧
      (exhaustion G e n).2 ⊆ (exhaustion G e m).2 := by
  apply inducedCode_mono
  intro v hv
  exact (mem_edgeBallCode G hG m v e).mpr
    (edgeBall_mono G e hnm ((mem_edgeBallCode G hG n v e).mp hv))

theorem isConnectedExhaustion (G : GraphCode) (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.val.1 e.val.2) :
    IsConnectedExhaustion G (exhaustion G e) := by
  have hfun : exhaustion G e = IntrinsicExhaustion.edgeBallSubgraph G hf e :=
    funext fun n => exhaustion_eq_edgeBallSubgraph G hf e n
  rw [hfun]
  exact IntrinsicExhaustion.isConnectedExhaustion_edgeBallSubgraph hc hf e he

end Problem336.Intrinsic

end

end OAI
