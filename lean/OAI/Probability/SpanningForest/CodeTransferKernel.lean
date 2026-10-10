import OAI.Probability.SpanningForest.ReducedCycleKernel

namespace OAI

noncomputable section

namespace Problem336
namespace CodeTransferKernel

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

def edgeEquiv (hK : IsFiniteConnectedSubgraph G K) : K.2 ≃ finiteCodeEdges K where
  toFun e := ⟨⟨e.1, (hK.2.1 e.1 e.2).2.2.1⟩, e.2⟩
  invFun e := ⟨e.1.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def incidence (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    Matrix {v : K.1 // v ≠ root} K.2 ℝ :=
  (ReducedLaplacian.reducedGradient (Problem336.codeSource hK)
    (Problem336.codeTarget hK) root).transpose

theorem incidence_eq_submatrix (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    incidence hK root =
      (ReducedCycleKernel.reducedFiniteIncidence K root).submatrix id (edgeEquiv hK) := by
  classical
  ext v e
  simp only [incidence, ReducedLaplacian.reducedGradient, Matrix.transpose_apply,
    ReducedCycleKernel.reducedFiniteIncidence, finiteIncidence, Matrix.submatrix_apply,
    edgeEquiv, Equiv.coe_fn_mk, id_eq, Problem336.codeSource, Problem336.codeTarget,
    Subtype.ext_iff]

theorem gram_submatrix {m n p : Type*} [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (e : p ≃ n) :
    A.submatrix id e * (A.submatrix id e).transpose = A * A.transpose := by
  change A.submatrix id e * A.transpose.submatrix e id = A * A.transpose
  simpa only [Matrix.submatrix_id_id] using
    Matrix.submatrix_mul_equiv A A.transpose id e id

theorem gram_eq_codeWeightedLaplacian (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) :
    (ReducedCycleKernel.reducedFiniteIncidence K root) *
        (ReducedCycleKernel.reducedFiniteIncidence K root).transpose =
      codeWeightedLaplacian hK root (fun _ => 1) := by
  classical
  rw [← gram_submatrix _ (edgeEquiv hK), ← incidence_eq_submatrix hK root]
  simp [incidence, codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian]

theorem transferMatrix_submatrix {m n p : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [Fintype p] (A : Matrix m n ℝ) (e : p ≃ n) :
    TransferProjection.transferMatrix (A.submatrix id e) =
      (TransferProjection.transferMatrix A).submatrix e e := by
  rw [TransferProjection.transferMatrix, gram_submatrix]
  change A.transpose.submatrix e id * (A * A.transpose)⁻¹ * A.submatrix id e = _
  ext i j
  rfl

theorem transfer_entry_eq_projection (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (e f : K.2) :
    TransferProjection.transferMatrix (incidence hK root) e f =
      inner ℝ (lp.single 2 (edgeEquiv hK e).1 (1 : ℝ))
        ((finiteHilbertEmbedding K).toLinearMap.range.starProjection
            (lp.single 2 (edgeEquiv hK f).1 (1 : ℝ)) -
          (finiteHilbertCycleSpace K).starProjection
            (lp.single 2 (edgeEquiv hK f).1 (1 : ℝ))) := by
  rw [incidence_eq_submatrix, transferMatrix_submatrix]
  exact ReducedCycleKernel.finite_transfer_entry_eq_projection hK root
    (edgeEquiv hK e) (edgeEquiv hK f)

end CodeTransferKernel
end Problem336

end

end OAI
