import OAI.NumberTheory.Catalan.Arithmetic.PrimeNonvanishing

namespace OAI

section

noncomputable section
open Matrix
open scoped BigOperators Kronecker

namespace InternalCatalan

theorem palindromicReducedBlockMatrix_conjugate {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicEigenChangeInv p ⊗ₖ (1 : Matrix (Fin 48) (Fin 48) (ZMod p))) *
        palindromicReducedBlockMatrix p *
        (palindromicEigenChange p ⊗ₖ (1 : Matrix (Fin 48) (Fin 48) (ZMod p))) =
      (1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ fixedB0Residue p +
        Matrix.diagonal (palindromicEigenLambda p) ⊗ₖ fixedB1Residue p := by
  simp only [palindromicReducedBlockMatrix, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    palindromicEigenChangeInv_mul hp2, palindromicEigenChange_diagonalizes hp2]

theorem palindromicEigenBlock_eq_reindexed_blockDiagonal (p : ℕ) [Fact p.Prime] :
    (1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ fixedB0Residue p +
        Matrix.diagonal (palindromicEigenLambda p) ⊗ₖ fixedB1Residue p =
      (Matrix.blockDiagonal (fun i : Fin p =>
        fixedB0Residue p + palindromicEigenLambda p i • fixedB1Residue p)).submatrix
          (Equiv.prodComm (Fin p) (Fin 48)) (Equiv.prodComm (Fin p) (Fin 48)) := by
  ext a b
  rcases a with ⟨i, r⟩
  rcases b with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    simp [Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [Matrix.submatrix_apply, Matrix.blockDiagonal_apply, hij]

theorem det_palindromicReducedBlockMatrix_eq_product {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (palindromicReducedBlockMatrix p).det =
      ∏ i : Fin p, (fixedB0Residue p + palindromicEigenLambda p i • fixedB1Residue p).det := by
  let U := palindromicEigenChangeInv p ⊗ₖ (1 : Matrix (Fin 48) (Fin 48) (ZMod p))
  let V := palindromicEigenChange p ⊗ₖ (1 : Matrix (Fin 48) (Fin 48) (ZMod p))
  have hUV : U * V = 1 := by
    dsimp [U, V]
    rw [← Matrix.mul_kronecker_mul, palindromicEigenChangeInv_mul hp2,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hdetUV : U.det * V.det = 1 := by
    rw [← Matrix.det_mul, hUV, Matrix.det_one]
  have hdet : (palindromicReducedBlockMatrix p).det =
      (U * palindromicReducedBlockMatrix p * V).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      _ = (U.det * V.det) * (palindromicReducedBlockMatrix p).det := by
        rw [hdetUV, one_mul]
      _ = _ := by ring
  calc
    _ = (U * palindromicReducedBlockMatrix p * V).det := hdet
    _ = ((1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ fixedB0Residue p +
        Matrix.diagonal (palindromicEigenLambda p) ⊗ₖ fixedB1Residue p).det := by
      rw [show U * palindromicReducedBlockMatrix p * V = _ from
        palindromicReducedBlockMatrix_conjugate hp2]
    _ = _ := by
      rw [palindromicEigenBlock_eq_reindexed_blockDiagonal,
        Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]

theorem det_palindromicReducedBlockMatrix_factorization
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicReducedBlockMatrix p).det =
      (fixedB0Residue p).det *
      (fixedB0Residue p + fixedB1Residue p).det ^ ((p - 1) / 2) *
      (fixedB0Residue p - fixedB1Residue p).det ^ ((p - 1) / 2) := by
  rw [det_palindromicReducedBlockMatrix_eq_product hp2]
  simpa only [zero_smul, add_zero, one_smul, neg_one_smul, ← sub_eq_add_neg] using
    (palindromicEigenvalue_product hp2
      (fun t : ZMod p => (fixedB0Residue p + t • fixedB1Residue p).det))

theorem det_palindromicResidueBlockMatrix_factorization
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (palindromicResidueBlockMatrix p).det =
      (palindromicTransitionMatrix p).det ^ 48 * (fixedB0Residue p).det *
      (fixedB0Residue p + fixedB1Residue p).det ^ ((p - 1) / 2) *
      (fixedB0Residue p - fixedB1Residue p).det ^ ((p - 1) / 2) := by
  rw [det_palindromicResidueBlockMatrix, det_palindromicReducedBlockMatrix_factorization hp2]
  ring

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem det_palindromicScaledResidueMatrix_factorization
    {p : ℕ} [Fact p.Prime] (hp : 260 < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    (palindromicScaledResidueMatrix z p).det =
      (palindromicTransitionMatrix p).det ^ 48 * (fixedB0Residue p).det *
      (fixedB0Residue p + fixedB1Residue p).det ^ ((p - 1) / 2) *
      (fixedB0Residue p - fixedB1Residue p).det ^ ((p - 1) / 2) := by
  rw [palindromicScaledResidueMatrix_eq_blocks hp z hz]
  exact det_palindromicResidueBlockMatrix_factorization (by omega)

theorem palindromic_original_determinant_residue_factorization
    {p : ℕ} [Fact p.Prime] (hp : 260 < p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    palindromicRatResidue p ((p : ℚ) ^ (2 * n p) * determinantRat z p) =
      (palindromicTransitionMatrix p).det ^ 48 * (fixedB0Residue p).det *
      (fixedB0Residue p + fixedB1Residue p).det ^ ((p - 1) / 2) *
      (fixedB0Residue p - fixedB1Residue p).det ^ ((p - 1) / 2) := by
  rw [← det_palindromicScaledRatMatrix z p]
  exact (palindromicScaledRatMatrix_det_residue z
    (palindromicScaledRatMatrix_entry_den_ne_zero hp z hz)).2.trans
      (det_palindromicScaledResidueMatrix_factorization hp z hz)

end InternalCatalan

end

end

end OAI
