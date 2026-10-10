import OAI.Analysis.KadisonKastler.BlockMatrices
import OAI.Analysis.KadisonKastler.CompletelyPositive
import OAI.Analysis.KadisonKastler.MatrixCorrection

namespace OAI

/-!
# Complete bounds for the off-diagonal commutator construction

Reordering the two finite matrix indices turns an amplification of
`b ↦ [0,-b;b,0]` into the same off-diagonal matrix over a matrix algebra.
Its norm is therefore exactly the norm of the original amplification.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The signed off-diagonal linear embedding used for paired representations. -/
def offDiagonalLinearMap : B →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) B where
  toFun b := blockOffDiagonal (-b) b
  map_add' b c := by
    ext i j
    simp only [CStarMatrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [blockOffDiagonal, add_comm]
  map_smul' z b := by
    ext i j
    simp only [CStarMatrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp [blockOffDiagonal]

omit [PartialOrder B] [StarOrderedRing B] in
theorem offDiagonalLinearMap_apply (b : B) :
    offDiagonalLinearMap b = blockOffDiagonal (-b) b := rfl

/-- Swap the finite amplification index and the two-by-two block index. -/
def matrixBlockSwap (n : Type*) [Fintype n] [DecidableEq n] :
    CStarMatrix n n (CStarMatrix (Fin 2) (Fin 2) B) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) (CStarMatrix n n B) :=
  (cstarMatrixComp n (Fin 2)).trans
    ((CStarMatrix.reindexₐ ℂ B (Equiv.prodComm n (Fin 2))).trans
      (cstarMatrixComp (Fin 2) n).symm)

theorem norm_matrixBlockSwap (n : Type*) [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n (CStarMatrix (Fin 2) (Fin 2) B)) :
    ‖matrixBlockSwap n X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixBlockSwap n) (matrixBlockSwap n).injective X

theorem matrixBlockSwap_offDiagonal (n : Type*) [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n B) :
    matrixBlockSwap n (CStarMatrix.mapₗ offDiagonalLinearMap X) =
      blockOffDiagonal (-X) X := by
  ext i j v w
  fin_cases i <;> fin_cases j <;> rfl

/-- The signed off-diagonal map preserves every square matrix norm. -/
theorem norm_map_offDiagonal_square {n : Type*} [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n B) :
    ‖CStarMatrix.mapₗ offDiagonalLinearMap X‖ = ‖X‖ := by
  rw [← norm_matrixBlockSwap n, matrixBlockSwap_offDiagonal, norm_blockOffDiagonal]
  simp

/-- The same exact norm identity holds for rectangular amplifications. -/
theorem norm_map_offDiagonal {m n : Type*} [Fintype m] [Fintype n]
    (X : CStarMatrix m n B) :
    ‖CStarMatrix.mapₗ offDiagonalLinearMap X‖ = ‖X‖ := by
  classical
  calc
    _ = ‖rectangularCorner (CStarMatrix.mapₗ offDiagonalLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ offDiagonalLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := norm_map_offDiagonal_square _
    _ = ‖X‖ := norm_rectangularCorner X

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The off-diagonal construction preserves exactly the complete bound. -/
theorem completelyBoundedBy_offDiagonal_iff (F : A →ₗ[ℂ] B) (e : ℝ) :
    CompletelyBoundedBy (offDiagonalLinearMap.comp F) e ↔ CompletelyBoundedBy F e := by
  constructor <;> intro h p q X
  · have hX := h p q X
    rwa [matrix_map_comp, norm_map_offDiagonal] at hX
  · rw [matrix_map_comp, norm_map_offDiagonal]
    exact h p q X

end

end KadisonKastler

end OAI
