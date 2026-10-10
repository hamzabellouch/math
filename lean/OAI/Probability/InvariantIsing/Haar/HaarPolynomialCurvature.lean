import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurve
import OAI.Probability.InvariantIsing.Haar.HaarHessianBound

namespace OAI

/-! The curvature inequality for polynomial observables, proved by finite algebra. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def matrixPolynomialDifferential {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun A := matrixPolynomialEval M (matrixPolynomialDerivation A p)
  map_add' A B := by simp
  map_smul' c A := by simp [Derivation.smul_apply]

lemma matrixPolynomial_hessian_bound {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    ((N : ℝ)-2)*(matrixPolynomialEval M (haarPolynomialGamma p p)) ≤
      ∑ i, ∑ j, ∑ k, ∑ l,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l)
          (matrixPolynomialDerivation (planeGenerator i j) p)))^2 := by
  let ell := matrixPolynomialDifferential p M
  let H : (Fin N × Fin N) → (Fin N × Fin N) → ℝ := fun a b =>
    matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))
  have hd (a b : Fin N × Fin N) : H a b-H b a =
      ell (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
        planeGenerator b.1 b.2*planeGenerator a.1 a.2) := by
    change matrixPolynomialEval M
        (matrixPolynomialDerivation (planeGenerator b.1 b.2)
          (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      matrixPolynomialEval M
        (matrixPolynomialDerivation (planeGenerator a.1 a.2)
          (matrixPolynomialDerivation (planeGenerator b.1 b.2) p)) =
      matrixPolynomialEval M (matrixPolynomialDerivation
        (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
          planeGenerator b.1 b.2*planeGenerator a.1 a.2) p)
    rw [← map_sub]
    exact congrArg (matrixPolynomialEval M) (Derivation.congr_fun
      (matrixPolynomialDerivation_commutator
        (planeGenerator b.1 b.2) (planeGenerator a.1 a.2)) p)
  have hb := sum_antisymmetric_square_le H
  simp_rw [hd] at hb
  simp only [Fintype.sum_prod_type] at hb
  rw [sum_plane_functional_double_bracket_sq ell] at hb
  have hg : (∑ i : Fin N, ∑ j : Fin N, (ell (planeGenerator i j))^2) =
      matrixPolynomialEval M (haarPolynomialGamma p p) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  rw [hg] at hb
  dsimp only [H] at hb
  linarith

/-- With the ordered-plane Laplacian, the Ricci lower bound is `N - 2`. -/
theorem matrixPolynomial_curvature {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    ((N : ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
        matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p)) := by
  have h := congrArg (matrixPolynomialEval M) (haarPolynomial_bochner_identity p)
  simp only [map_mul,map_ofNat,map_add,map_sum,map_pow] at h
  have hb := matrixPolynomial_hessian_bound p M
  linarith

end InvariantIsing

end

end OAI
