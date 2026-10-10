import OAI.Analysis.KadisonKastler.MatrixCornerConjugation

namespace OAI

/-! # The two-term diagonal average in Cuntz coordinates -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CuntzFamily

variable (S : CuntzFamily (Fin 2) H)

theorem matrix_conjugate_liftedTwoBlockUnitary (u v : unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    S.matrix (unitaryConj (S.liftedTwoBlockUnitary u v) T) =
      blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H) * S.matrix T *
        star (blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H)) := by
  change S.matrixHom ((_ : H →L[ℂ] H) * T * star (_ : H →L[ℂ] H)) = _
  rw [map_mul, map_mul, map_star]
  change S.matrix _ * S.matrix T * star (S.matrix _) = _
  rw [S.matrix_liftedTwoBlockUnitary]

theorem matrix_diagonal_average (T : H →L[ℂ] H) :
    S.matrix ((1 / 2 : ℝ) • T + (1 / 2 : ℝ) •
      unitaryConj (S.liftedTwoBlockUnitary 1 (-1)) T) =
      blockDiagonal (S.matrix T 0 0) (S.matrix T 1 1) := by
  have hlin : S.matrix ((1 / 2 : ℝ) • T + (1 / 2 : ℝ) •
      unitaryConj (S.liftedTwoBlockUnitary 1 (-1)) T) =
      (1 / 2 : ℝ) • S.matrix T + (1 / 2 : ℝ) •
        S.matrix (unitaryConj (S.liftedTwoBlockUnitary 1 (-1)) T) := by
    ext i j
    simp only [matrix, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rfl
  rw [hlin, S.matrix_conjugate_liftedTwoBlockUnitary]
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CStarMatrix.add_apply, CStarMatrix.smul_apply, CStarMatrix.mul_apply,
      CStarMatrix.star_apply, Fin.sum_univ_two, blockDiagonal, diagonalStarAlgHom_apply,
      Unitary.coe_neg] <;> module

theorem exists_diagonal_average_mem (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (T : H →L[ℂ] H) (hT : T ∈ K) :
    ∃ V ∈ K, S.matrix V = blockDiagonal (S.matrix T 0 0) (S.matrix T 1 1) := by
  let W : unitary (H →L[ℂ] H) := S.liftedTwoBlockUnitary 1 (-1)
  have hW : (W : H →L[ℂ] H) ∈ N := S.liftedTwoBlockUnitary_mem N hS 1 (-1)
    N.one_mem (N.neg_mem N.one_mem)
  have hin : unitaryConj W T ∈ K := hinv (algebraUnitaryOfMem W hW) T hT
  refine ⟨(1 / 2 : ℝ) • T + (1 / 2 : ℝ) • unitaryConj W T,
    hK hT hin (by norm_num) (by norm_num) (by norm_num), S.matrix_diagonal_average T⟩

end CuntzFamily

end

end KadisonKastler

end OAI
