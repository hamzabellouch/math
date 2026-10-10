import OAI.Probability.SpanningForest.GraphFreeKernel
import OAI.Probability.SpanningForest.FiniteCycleIncidence

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FreeKernel

open CoordinateTruncation

theorem finiteHilbertEmbedding_mem_supported (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    finiteHilbertEmbedding K x ∈ supported (finiteEdges K : Set EdgeCode) := by
  change finiteHilbertEmbeddingLinear K x ∈ supported (finiteEdges K : Set EdgeCode)
  rw [finiteHilbertEmbeddingLinear_sum]
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem
  exact single_mem_supported ((mem_finiteEdges K e.1).mpr e.2) 1

@[simp] theorem truncate_finiteHilbertEmbedding (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    truncate (finiteEdges K) (finiteHilbertEmbedding K x) = finiteHilbertEmbedding K x := by
  rw [← starProjection_supported]
  exact Submodule.starProjection_eq_self_iff.mpr (finiteHilbertEmbedding_mem_supported K x)

theorem finiteKernel_embedding {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    finiteKernel K (finiteHilbertEmbedding K x) =
      finiteHilbertEmbedding K
        (x - (LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))).starProjection x) := by
  let C := LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))
  have hmap : C.map (finiteHilbertEmbedding K).toLinearMap = finiteHilbertCycleSpace K :=
    hK.finiteHilbertCycleSpace_eq_euclideanKernel.symm
  have : (C.map (finiteHilbertEmbedding K).toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  have hp := (finiteHilbertEmbedding K).map_starProjection C x
  have hp' : finiteHilbertEmbedding K (C.starProjection x) =
      (finiteHilbertCycleSpace K).starProjection (finiteHilbertEmbedding K x) := by
    simpa only [hmap] using hp
  change truncate (finiteEdges K) (finiteHilbertEmbedding K x) -
    (finiteHilbertCycleSpace K).starProjection (finiteHilbertEmbedding K x) =
      finiteHilbertEmbedding K (x - C.starProjection x)
  rw [truncate_finiteHilbertEmbedding, ← hp', map_sub]

theorem finiteKernel_embedding_inner {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K)
    (x y : EuclideanSpace ℝ (finiteCodeEdges K)) :
    inner ℝ (finiteHilbertEmbedding K x) (finiteKernel K (finiteHilbertEmbedding K y)) =
      inner ℝ x
        (y - (LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))).starProjection y) := by
  rw [finiteKernel_embedding hK]
  exact (finiteHilbertEmbedding K).inner_map_map _ _

@[simp] theorem finiteHilbertEmbedding_single (K : FiniteSubgraphCode)
    (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K (EuclideanSpace.single e (1 : ℝ)) = edgeVector e.1 := by
  change finiteHilbertEmbeddingLinear K (EuclideanSpace.single e (1 : ℝ)) = edgeVector e.1
  rw [finiteHilbertEmbeddingLinear_sum]
  simp [EuclideanSpace.single, PiLp.single_apply, edgeVector]

theorem finiteKernel_basis_minor_eq {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → finiteCodeEdges K) :
    Matrix.det (fun i j => inner ℝ (edgeVector (e i).1)
      (finiteKernel K (edgeVector (e j).1))) =
    Matrix.det (fun i j => inner ℝ (EuclideanSpace.single (e i) (1 : ℝ))
      (EuclideanSpace.single (e j) (1 : ℝ) -
        (LinearMap.ker (Matrix.toEuclideanLin (finiteIncidence K))).starProjection
          (EuclideanSpace.single (e j) (1 : ℝ)))) := by
  congr 1
  funext i j
  rw [← finiteHilbertEmbedding_single K (e i), ← finiteHilbertEmbedding_single K (e j)]
  exact finiteKernel_embedding_inner hK _ _

end Problem336.FreeKernel

end

end OAI
