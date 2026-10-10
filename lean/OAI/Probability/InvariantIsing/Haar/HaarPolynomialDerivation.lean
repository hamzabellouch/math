import OAI.Probability.InvariantIsing.Haar.HaarFrobeniusBracket
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie

namespace OAI

/-! Polynomial directional derivatives for left matrix multiplication. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

abbrev MatrixPolynomial (N : ℕ) := MvPolynomial (Fin N × Fin N) ℝ

/-- Differentiate a matrix polynomial along the vector field `U ↦ A U`. -/
def matrixPolynomialDerivation {N : ℕ} :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Derivation ℝ (MatrixPolynomial N) (MatrixPolynomial N) where
  toFun A := MvPolynomial.mkDerivation ℝ fun ij =>
    ∑ k, A ij.1 k • MvPolynomial.X (k,ij.2)
  map_add' A B := by
    apply MvPolynomial.derivation_ext
    intro ij
    simp [MvPolynomial.mkDerivation_X,Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c A := by
    apply MvPolynomial.derivation_ext
    intro ij
    simp [MvPolynomial.mkDerivation_X,Matrix.smul_apply,smul_smul,Finset.smul_sum]

@[simp] lemma matrixPolynomialDerivation_X {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialDerivation A (X (i,j)) = ∑ k, A i k • X (k,j) :=
  MvPolynomial.mkDerivation_X _ _ _

lemma matrixPolynomialDerivation_mul_X {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialDerivation A (matrixPolynomialDerivation B (X (i,j))) =
      matrixPolynomialDerivation (B*A) (X (i,j)) := by
  simp only [matrixPolynomialDerivation_X,map_sum,Derivation.map_smul_of_tower,Finset.smul_sum,
    smul_smul,Matrix.mul_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Left matrix vector fields give the opposite matrix Lie bracket. -/
theorem matrixPolynomialDerivation_commutator {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) :
    ⁅matrixPolynomialDerivation A,matrixPolynomialDerivation B⁆ =
      matrixPolynomialDerivation (B*A-A*B) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,j⟩
  rw [Derivation.commutator_apply,matrixPolynomialDerivation_mul_X,
    matrixPolynomialDerivation_mul_X,map_sub,Derivation.sub_apply]

@[simp] lemma matrixPolynomialDerivation_plane_X {N : ℕ} (i j k l : Fin N) :
    matrixPolynomialDerivation (planeGenerator i j) (X (k,l)) =
      (if k=i then X (j,l) else 0)-(if k=j then X (i,l) else 0) := by
  simp [matrixPolynomialDerivation_X,planeGenerator,Matrix.single_apply,ite_and,eq_comm]

end InvariantIsing

end

end OAI
