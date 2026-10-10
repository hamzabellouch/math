import OAI.Analysis.KadisonKastler.PositiveCornerSquare

namespace OAI

/-! # Strict diagonal contraction in two-by-two coordinates -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def firstBlockProjection : CStarMatrix (Fin 2) (Fin 2) A := blockDiagonal 1 0

theorem firstBlockProjection_isStarProjection :
    IsStarProjection (firstBlockProjection (A := A)) := by
  constructor
  · ext i j
    simp only [firstBlockProjection, CStarMatrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]
  · ext i j
    simp only [firstBlockProjection, CStarMatrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]

theorem secondBlockProjection_eq :
    1 - firstBlockProjection (A := A) = blockDiagonal 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem lowerLeft_column_square (T : CStarMatrix (Fin 2) (Fin 2) A) :
    star ((1 - firstBlockProjection) * (T * firstBlockProjection)) *
        ((1 - firstBlockProjection) * (T * firstBlockProjection)) =
      blockDiagonal (star (T 1 0) * T 1 0) 0 := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem upperRight_column_square (T : CStarMatrix (Fin 2) (Fin 2) A) :
    star (firstBlockProjection * (T * (1 - firstBlockProjection))) *
        (firstBlockProjection * (T * (1 - firstBlockProjection))) =
      blockDiagonal 0 (star (T 0 1) * T 0 1) := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

theorem two_corner_diagonal_eq (T : CStarMatrix (Fin 2) (Fin 2) A) :
    firstBlockProjection * T * firstBlockProjection +
      (1 - firstBlockProjection) * T * (1 - firstBlockProjection) =
      blockDiagonal (T 0 0) (T 1 1) := by
  rw [secondBlockProjection_eq]
  ext i j
  simp only [CStarMatrix.add_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply]

variable [PartialOrder A] [StarOrderedRing A]

local instance matrixStrictContractionInstance1 : LE (CStarMatrix (Fin 2) (Fin 2) A) :=
  (CStarAlgebra.spectralOrder (CStarMatrix (Fin 2) (Fin 2) A)).toLE
local instance matrixStrictContractionInstance2 : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance matrixStrictContractionInstance3 : Preorder (CStarMatrix (Fin 2) (Fin 2) A) :=
  (CStarAlgebra.spectralOrder (CStarMatrix (Fin 2) (Fin 2) A)).toPreorder
local instance matrixStrictContractionInstance4 : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrderedRing _

theorem blockDiagonal_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ blockDiagonal a b := by
  have he : blockDiagonal a b = star (blockDiagonal (CFC.sqrt a) (CFC.sqrt b)) *
      blockDiagonal (CFC.sqrt a) (CFC.sqrt b) := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [blockDiagonal, diagonalStarAlgHom_apply, (CFC.sqrt_nonneg a).star_eq,
        (CFC.sqrt_nonneg b).star_eq, CFC.sqrt_mul_sqrt_self a ha,
        CFC.sqrt_mul_sqrt_self b hb]
  rw [he]
  exact star_mul_self_nonneg _

theorem blockDiagonal_mono {a b c d : A} (hac : a ≤ c) (hbd : b ≤ d) :
    blockDiagonal a b ≤ blockDiagonal c d := by
  have he : blockDiagonal c d - blockDiagonal a b = blockDiagonal (c - a) (d - b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, diagonalStarAlgHom_apply]
  rw [← sub_nonneg, he]
  exact blockDiagonal_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hbd)

theorem norm_matrix_diagonal_lt_of_positive_corner [Nontrivial A]
    (T : CStarMatrix (Fin 2) (Fin 2) A) (hT : IsSelfAdjoint T)
    (δ : ℝ) (hδ : 0 < δ) (hc : algebraMap ℝ A δ ≤ T 0 1) :
    ‖blockDiagonal (T 0 0) (T 1 1)‖ < ‖T‖ := by
  have hd : 0 ≤ algebraMap ℝ A δ := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg hδ.le (zero_le_one : (0 : A) ≤ 1)
  have hsa : IsSelfAdjoint (T 0 1) := (hd.trans hc).isSelfAdjoint
  have hentry : T 1 0 = T 0 1 := by
    have he := congrArg (fun X : CStarMatrix (Fin 2) (Fin 2) A => X 1 0) hT.star_eq
    exact he.symm.trans hsa.star_eq
  have hsq := scalar_sq_le_star_mul_of_scalar_le (T 0 1) δ hδ.le hc
  have hδnorm : δ ≤ ‖T‖ := by
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hc hd
    have he : ‖algebraMap ℝ A δ‖ = δ := by
      rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos hδ]
    rw [he] at hn
    exact hn.trans (CStarMatrix.norm_entry_le_norm (M := T) (i := 0) (j := 1))
  have hpq : δ ^ 2 • firstBlockProjection (A := A) ≤
      star ((1 - firstBlockProjection) * (T * firstBlockProjection)) *
        ((1 - firstBlockProjection) * (T * firstBlockProjection)) := by
    rw [lowerLeft_column_square, hentry]
    convert blockDiagonal_mono hsq (le_refl (0 : A)) using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstBlockProjection, blockDiagonal, diagonalStarAlgHom_apply,
        Algebra.algebraMap_eq_smul_one]
  have hqp : δ ^ 2 • (1 - firstBlockProjection (A := A)) ≤
      star (firstBlockProjection * (T * (1 - firstBlockProjection))) *
        (firstBlockProjection * (T * (1 - firstBlockProjection))) := by
    rw [upperRight_column_square, secondBlockProjection_eq]
    convert blockDiagonal_mono (le_refl (0 : A)) hsq using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockDiagonal, diagonalStarAlgHom_apply, Algebra.algebraMap_eq_smul_one]
  have hh := norm_two_corner_diagonal_lt firstBlockProjection T
    firstBlockProjection_isStarProjection hT δ hδ hδnorm hpq hqp
  rwa [two_corner_diagonal_eq] at hh

end

end KadisonKastler

end OAI
