import OAI.Probability.SpanningForest.ReducedCycleKernel
import OAI.Probability.SpanningForest.FiniteKernelEmbedding

namespace OAI

noncomputable section
open scoped BigOperators Topology
namespace Problem336.FiniteKernelBridge
open CoordinateTruncation

theorem embedding_range (K : FiniteSubgraphCode) :
    (finiteHilbertEmbedding K).toLinearMap.range =
      supported (finiteEdges K : Set EdgeCode) := by
  classical
  apply le_antisymm
  · rintro x ⟨y, rfl⟩ e he
    exact FreeKernel.finiteHilbertEmbedding_mem_supported K y e he
  · intro x hx
    refine ⟨WithLp.toLp 2 (fun e : finiteCodeEdges K => x e.1), ?_⟩
    apply lp.ext
    funext e
    by_cases he : e ∈ finiteEdges K
    · exact finiteHilbertEmbedding_apply K _ ⟨e, (mem_finiteEdges K e).mp he⟩
    · exact (FreeKernel.finiteHilbertEmbedding_mem_supported K _ e he).trans (hx e he).symm

theorem embedding_projection (K : FiniteSubgraphCode) :
    (finiteHilbertEmbedding K).toLinearMap.range.starProjection =
      truncate (finiteEdges K) := by
  simpa only [embedding_range] using (starProjection_supported (𝕜 := ℝ) (finiteEdges K))

theorem transfer_entry_eq_finiteKernel {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) (e f : finiteCodeEdges K) :
    TransferProjection.transferMatrix (ReducedCycleKernel.reducedFiniteIncidence K root) e f =
      inner ℝ (FreeKernel.edgeVector e.1)
        (FreeKernel.finiteKernel K (FreeKernel.edgeVector f.1)) := by
  rw [ReducedCycleKernel.finite_transfer_entry_eq_projection hK root,
    embedding_projection]
  rfl

theorem transfer_operator_eq_finiteKernel {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) (x : EdgeHilbert) :
    finiteHilbertEmbedding K
      ((TransferProjection.transferMatrix (ReducedCycleKernel.reducedFiniteIncidence K root)).toEuclideanLin
        ((finiteHilbertEmbedding K).toContinuousLinearMap.adjoint x)) =
      FreeKernel.finiteKernel K x := by
  rw [ReducedCycleKernel.finite_transfer_eq_coordinate_sub_cycle_of_connected hK root,
    embedding_projection]
  rfl

theorem transfer_minor_eq_finiteKernel {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → finiteCodeEdges K) :
    Matrix.det (fun i j =>
      TransferProjection.transferMatrix (ReducedCycleKernel.reducedFiniteIncidence K root) (e i) (e j)) =
    Matrix.det (fun i j => inner ℝ (FreeKernel.edgeVector (e i).1)
      (FreeKernel.finiteKernel K (FreeKernel.edgeVector (e j).1))) := by
  congr 1
  funext i j
  exact transfer_entry_eq_finiteKernel hK root (e i) (e j)

end Problem336.FiniteKernelBridge

end

end OAI
