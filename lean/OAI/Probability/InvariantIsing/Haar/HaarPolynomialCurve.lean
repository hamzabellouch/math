import OAI.Probability.InvariantIsing.Haar.HaarPolynomialDerivation
import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation

namespace OAI

/-! Evaluation of polynomial Lie derivatives on genuine matrix curves. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def matrixPolynomialEval {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    MatrixPolynomial N →ₐ[ℝ] ℝ :=
  MvPolynomial.aeval fun ij => M ij.1 ij.2

@[simp] lemma matrixPolynomialEval_X {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialEval M (X (i,j)) = M i j :=
  MvPolynomial.aeval_X _ _

@[simp] lemma matrixPolynomialEval_C {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    matrixPolynomialEval M (C c) = c :=
  MvPolynomial.aeval_C _ _

theorem hasDerivAt_matrixPolynomialEval {N : ℕ}
    (p : MatrixPolynomial N) (M : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) ((A*M t) i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (M s) p)
      (matrixPolynomialEval (M t) (matrixPolynomialDerivation A p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq =>
    convert hp.add hq using 1
    all_goals simp only [map_add]
    all_goals rfl
  | mul_X p ij hp =>
    rcases ij with ⟨i,j⟩
    have hx : matrixPolynomialEval (M t)
        (matrixPolynomialDerivation A (X (i,j))) = (A*M t) i j := by
      simp only [matrixPolynomialDerivation_X,map_sum,map_smul,
        matrixPolynomialEval_X,smul_eq_mul,Matrix.mul_apply]
    convert hp.mul (hM i j) using 1
    · simp only [map_mul,matrixPolynomialEval_X]
      rfl
    · rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,
        hx,matrixPolynomialEval_X]
      ring

end InvariantIsing

end

end OAI
