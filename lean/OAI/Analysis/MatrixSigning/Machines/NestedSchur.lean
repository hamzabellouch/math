import Mathlib

namespace OAI

section

namespace KS.W30

theorem nested_schur_invOf {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (F : Matrix ι ρ ℚ) (G : Matrix κ ρ ℚ)
    (H : Matrix ρ ι ℚ) (I : Matrix ρ κ ℚ) (J : Matrix ρ ρ ℚ)
    [Invertible A] [Invertible (D - C * ⅟A * B)]
    [Invertible (Matrix.fromBlocks A B C D)] :
    J - Matrix.fromCols H I * ⅟(Matrix.fromBlocks A B C D) * Matrix.fromRows F G =
      (J - H * ⅟A * F) -
        (I - H * ⅟A * B) * ⅟(D - C * ⅟A * B) * (G - C * ⅟A * F) := by
  rw [Matrix.invOf_fromBlocks₁₁_eq, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  generalize ⅟(D - C * ⅟A * B) = R
  generalize ⅟A = P
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

theorem nested_schur {ι κ ρ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (F : Matrix ι ρ ℚ) (G : Matrix κ ρ ℚ)
    (H : Matrix ρ ι ℚ) (I : Matrix ρ κ ℚ) (J : Matrix ρ ρ ℚ)
    (hA : A.det ≠ 0) (hS : (D - C * A⁻¹ * B).det ≠ 0) :
    J - Matrix.fromCols H I * (Matrix.fromBlocks A B C D)⁻¹ * Matrix.fromRows F G =
      (J - H * A⁻¹ * F) -
        (I - H * A⁻¹ * B) * (D - C * A⁻¹ * B)⁻¹ * (G - C * A⁻¹ * F) := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  let : Invertible (D - C * ⅟A * B) := Matrix.invertibleOfIsUnitDet _ (by
    simpa only [Matrix.invOf_eq_nonsing_inv] using (isUnit_iff_ne_zero.mpr hS))
  let : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv] using nested_schur_invOf A B C D F G H I J

end KS.W30

end

end OAI
