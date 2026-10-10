import OAI.Probability.InvariantIsing.Haar.HaarPolynomialDerivation
import OAI.Probability.InvariantIsing.Haar.HaarCasimirAlgebra

namespace OAI

/-! The polynomial Laplacian on the orthogonal group commutes with rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def matrixPolynomialOperator {N : ℕ} :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Module.End ℝ (MatrixPolynomial N) where
  toFun A := (matrixPolynomialDerivation A).toLinearMap
  map_add' A B := by ext p; simp
  map_smul' c A := by ext p; simp

@[simp] lemma matrixPolynomialOperator_apply {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (p : MatrixPolynomial N) :
    matrixPolynomialOperator A p = matrixPolynomialDerivation A p := rfl

lemma matrixPolynomialOperator_commutator {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialOperator A*matrixPolynomialOperator B-
      matrixPolynomialOperator B*matrixPolynomialOperator A =
      matrixPolynomialOperator (B*A-A*B) := by
  apply LinearMap.ext
  intro p
  exact Derivation.congr_fun (matrixPolynomialDerivation_commutator A B) p

lemma commutator_square_identity {R : Type*} [Ring R] (X Y : R) :
    X*(Y*Y)-(Y*Y)*X = -(Y*(Y*X-X*Y)+(Y*X-X*Y)*Y) := by
  noncomm_ring

/-- Ordered coordinate planes; its carré du champ is the sum of the ordered squares. -/
def haarPolynomialLaplacian (N : ℕ) : Module.End ℝ (MatrixPolynomial N) :=
  ∑ i, ∑ j, matrixPolynomialOperator (planeGenerator i j)*
    matrixPolynomialOperator (planeGenerator i j)

theorem haarPolynomialLaplacian_commutes {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    matrixPolynomialOperator A*haarPolynomialLaplacian N =
      haarPolynomialLaplacian N*matrixPolynomialOperator A := by
  apply sub_eq_zero.mp
  have he (i j : Fin N) :
      matrixPolynomialOperator A*
          (matrixPolynomialOperator (planeGenerator i j)*matrixPolynomialOperator (planeGenerator i j))-
        (matrixPolynomialOperator (planeGenerator i j)*matrixPolynomialOperator (planeGenerator i j))*
          matrixPolynomialOperator A =
      -(matrixPolynomialOperator (planeGenerator i j)*
            matrixPolynomialOperator (A*planeGenerator i j-planeGenerator i j*A)+
        matrixPolynomialOperator (A*planeGenerator i j-planeGenerator i j*A)*
            matrixPolynomialOperator (planeGenerator i j)) := by
    rw [← matrixPolynomialOperator_commutator (planeGenerator i j) A]
    exact commutator_square_identity _ _
  simp only [haarPolynomialLaplacian,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]
  rw [plane_adjoint_jordan_sum matrixPolynomialOperator A hA,neg_zero]

lemma haarPolynomialLaplacian_apply {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N p = ∑ i : Fin N, ∑ j : Fin N,
      matrixPolynomialDerivation (planeGenerator i j)
        (matrixPolynomialDerivation (planeGenerator i j) p) := by
  simp only [haarPolynomialLaplacian,LinearMap.sum_apply,Module.End.mul_apply,
    matrixPolynomialOperator_apply]

lemma haarPolynomialLaplacian_derivation {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (matrixPolynomialDerivation A p) =
      matrixPolynomialDerivation A (haarPolynomialLaplacian N p) := by
  exact (LinearMap.congr_fun (haarPolynomialLaplacian_commutes A hA) p).symm

end InvariantIsing

end

end OAI
