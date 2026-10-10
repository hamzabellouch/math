import OAI.Probability.SpanningForest.CodedInclusion
import OAI.Probability.SpanningForest.FiniteKernelBridge

namespace OAI

noncomputable section
open scoped Matrix
namespace Problem336.CodedTransferBridge
variable {G : GraphCode} {K : FiniteSubgraphCode}

def edgeEquiv (hK : IsFiniteConnectedSubgraph G K) : finiteCodeEdges K ≃ K.2 where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, (hK.2.1 e.1 e.2).2.2.1⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidence_eq_submatrix (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    ReducedCycleKernel.reducedFiniteIncidence K root =
      (codeIncidence hK root).submatrix id (edgeEquiv hK) := by
  classical
  ext v e
  simp [ReducedCycleKernel.reducedFiniteIncidence, finiteIncidence,
    codeIncidence, ReducedLaplacian.reducedGradient, Matrix.transpose_apply,
    Matrix.submatrix_apply, codeSource, codeTarget, edgeEquiv, Subtype.ext_iff, id_eq]

theorem gram_eq_laplacian (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    ReducedCycleKernel.reducedFiniteIncidence K root *
      (ReducedCycleKernel.reducedFiniteIncidence K root).transpose =
        codeWeightedLaplacian hK root (fun _ => 1) := by
  classical
  rw [incidence_eq_submatrix hK root, Matrix.transpose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp [codeIncidence, codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian]

theorem current_entry_eq_transfer (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root (fun _ => 1) S e f =
      TransferProjection.transferMatrix (ReducedCycleKernel.reducedFiniteIncidence K root)
        ((edgeEquiv hK).symm e.1) ((edgeEquiv hK).symm f.1) := by
  classical
  unfold TransferProjection.transferMatrix
  rw [gram_eq_laplacian hK root]
  simp only [codeTransferCurrent, Matrix.diagonal_one, Matrix.one_mul,
    incidence_eq_submatrix hK root, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply]

theorem current_entry_eq_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root (fun _ => 1) S e f =
      inner ℝ (FreeKernel.edgeVector ((edgeEquiv hK).symm e.1).1)
        (FreeKernel.finiteKernel K (FreeKernel.edgeVector ((edgeEquiv hK).symm f.1).1)) := by
  rw [current_entry_eq_transfer]
  exact FiniteKernelBridge.transfer_entry_eq_finiteKernel hK root _ _

theorem current_det_eq_finiteKernel (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (S : Finset K.2) :
    (codeTransferCurrent hK root (fun _ => 1) S).det =
      Matrix.det (fun e f : S =>
        inner ℝ (FreeKernel.edgeVector ((edgeEquiv hK).symm e.1).1)
          (FreeKernel.finiteKernel K (FreeKernel.edgeVector ((edgeEquiv hK).symm f.1).1))) := by
  congr 1
  funext e f
  exact current_entry_eq_finiteKernel hK root S e f
end Problem336.CodedTransferBridge

end

end OAI
