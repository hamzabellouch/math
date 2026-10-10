import OAI.Probability.InvariantIsing.Cavity.CavityBaseEigenspaces
import OAI.Probability.InvariantIsing.Haar.MatrixRotation

namespace OAI

/-! Quadratic energies in physical coordinates and after deleting the
annihilated cavity rows and columns. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_conjugate {r d : ℕ}
    (U : Matrix (Fin r) (Fin d) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin d → ℝ) :
    cavityQuadratic (U.transpose * A * U) x = cavityQuadratic A (U *ᵥ x) := by
  rw [cavityQuadratic_dotProduct, cavityQuadratic_dotProduct,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

lemma cavityQuadratic_first_block {N n : ℕ}
    (A : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)
    (hrow : ∀ j i, A (Fin.natAdd N j) i = 0)
    (hcol : ∀ i j, A i (Fin.natAdd N j) = 0)
    (x : Fin (N+n) → ℝ) :
    cavityQuadratic A x =
      cavityQuadratic (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
        (fun i => x (Fin.castAdd n i)) := by
  simp only [cavityQuadratic, Fin.sum_univ_add, hrow, hcol, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, Matrix.submatrix_apply]

lemma cavityQuadratic_first_block_of_symmetric {N n : ℕ}
    (A : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) (hA : A.transpose = A)
    (hcol : ∀ i j, A i (Fin.natAdd N j) = 0) (x : Fin (N+n) → ℝ) :
    cavityQuadratic A x =
      cavityQuadratic (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
        (fun i => x (Fin.castAdd n i)) := by
  apply cavityQuadratic_first_block A _ hcol x
  intro j i
  rw [← hA]
  exact hcol i j

lemma cavityQuadratic_diagonal {d : ℕ} (a x : Fin d → ℝ) :
    cavityQuadratic (Matrix.diagonal a) x = (1 / 2 : ℝ) * ∑ i, a i * (x i)^2 := by
  rw [cavityQuadratic_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cavity_rotatedEnergy_matrix {N : ℕ} (eig : Fin N → ℝ)
    (U : Orthogonal N) (σ : Spin N) :
    rotatedEnergy eig (matrixRotation U) σ =
      cavityQuadratic ((U : Matrix (Fin N) (Fin N) ℝ).transpose *
        Matrix.diagonal eig * (U : Matrix (Fin N) (Fin N) ℝ))
          (fun i => spinValue (σ i)) := by
  rw [cavityQuadratic_conjugate, cavityQuadratic_diagonal]
  rfl

lemma cavityQuadratic_inverse_rotation {N : ℕ} (eig : Fin N → ℝ)
    (V : Orthogonal N) (σ : Spin N) :
    cavityQuadratic ((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal eig *
      (V : Matrix (Fin N) (Fin N) ℝ).transpose) (fun i => spinValue (σ i)) =
      rotatedEnergy eig (matrixRotation V⁻¹) σ := by
  rw [cavity_rotatedEnergy_matrix]
  rfl

lemma cavityBaseReplacement_transpose {r s d : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J.transpose = J) (hD : D.transpose = D) (hA₀ : A₀.transpose = A₀) :
    (cavityBaseReplacement J W D B A₀).transpose = cavityBaseReplacement J W D B A₀ := by
  simp only [cavityBaseReplacement, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose, hJ, hD, hA₀, Matrix.mul_assoc]

end InvariantIsing

end

end OAI
