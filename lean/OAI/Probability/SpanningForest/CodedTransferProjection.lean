import OAI.Probability.SpanningForest.CodeTransferKernel
import OAI.Probability.SpanningForest.CodedInclusion
import OAI.Probability.SpanningForest.FiniteKernelBridge

namespace OAI

noncomputable section

namespace Problem336
namespace CodeTransferKernel

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem codeTransferCurrent_one (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    codeTransferCurrent hK root (fun _ => 1) S =
      (TransferProjection.transferMatrix (incidence hK root)).submatrix
        (Subtype.val : S → K.2) (Subtype.val : S → K.2) := by
  classical
  simp only [codeTransferCurrent, Matrix.diagonal_one, Matrix.one_mul,
    codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian, Matrix.mul_one,
    TransferProjection.transferMatrix, incidence, codeIncidence,
    Matrix.transpose_transpose]
  rfl

theorem codeTransferCurrent_one_entry (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root (fun _ => 1) S e f =
      inner ℝ (lp.single 2 (edgeEquiv hK e.1).1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection
            (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection
            (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ))) := by
  rw [codeTransferCurrent_one]
  exact transfer_entry_eq_projection hK root e.1 f.1

theorem code_tree_inclusion_ratio_projection (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    (((spanningTrees K).filter
      (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T)).card : ℝ) /
        (spanningTrees K).card =
      Matrix.det (fun e f : S =>
        inner ℝ (lp.single 2 (edgeEquiv hK e.1).1 (1 : ℝ))
          ((finiteHilbertEmbedding K).toLinearMap.range.starProjection
              (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ)) -
            (finiteHilbertCycleSpace K).starProjection
              (lp.single 2 (edgeEquiv hK f.1).1 (1 : ℝ)))) := by
  have h := code_tree_inclusion_ratio hK root (fun _ => 1) (fun _ => by norm_num) S
  simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  congr 1
  ext e f
  exact codeTransferCurrent_one_entry hK root S e f

theorem codeTransferCurrent_one_eq_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    codeTransferCurrent hK root (fun _ => 1) S =
      fun e f : S => inner ℝ (FreeKernel.edgeVector (edgeEquiv hK e.1).1)
        (FreeKernel.finiteKernel K (FreeKernel.edgeVector (edgeEquiv hK f.1).1)) := by
  ext e f
  rw [codeTransferCurrent_one_entry, FiniteKernelBridge.embedding_projection]
  rfl

theorem code_tree_inclusion_ratio_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    (((spanningTrees K).filter
      (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T)).card : ℝ) /
        (spanningTrees K).card =
      Matrix.det (fun e f : S =>
        inner ℝ (FreeKernel.edgeVector (edgeEquiv hK e.1).1)
          (FreeKernel.finiteKernel K (FreeKernel.edgeVector (edgeEquiv hK f.1).1))) := by
  have h := code_tree_inclusion_ratio hK root (fun _ => 1) (fun _ => by norm_num) S
  simpa only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    codeTransferCurrent_one_eq_finiteKernel] using h

end CodeTransferKernel
end Problem336

end

end OAI
