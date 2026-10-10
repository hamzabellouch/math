import OAI.Probability.SLE.Angle.AngleEigenPolynomials
import Mathlib.Algebra.Polynomial.Sequence

namespace OAI

/-! The polynomial eigenfunctions form a basis, since each is monic of
its prescribed degree. This will identify transition laws from moments. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def angleEigenSequence (κ : ℝ) : Polynomial.Sequence ℝ where
  elems' := angleEigenPolynomial κ
  degree_eq' n := by
    rw [degree_eq_natDegree (angleEigenPolynomial_monic κ n).ne_zero,
      angleEigenPolynomial_natDegree]

def angleEigenBasis (κ : ℝ) : Module.Basis ℕ ℝ ℝ[X] :=
  (angleEigenSequence κ).basis (fun n => by
    change IsUnit (angleEigenPolynomial κ n).leadingCoeff
    rw [show (angleEigenPolynomial κ n).leadingCoeff=1 from angleEigenPolynomial_monic κ n]
    exact isUnit_one)

lemma angleEigenBasis_apply (κ : ℝ) (n : ℕ) :
    angleEigenBasis κ n=angleEigenPolynomial κ n := by
  exact Polynomial.Sequence.basis_eq_self _ _ n

lemma angleEigenBasis_eigen {κ : ℝ} (hκ : 0<κ) (n : ℕ) :
    anglePolynomialGenerator κ (angleEigenBasis κ n)=
      -C (anglePolynomialEigenvalue κ n)*angleEigenBasis κ n := by
  simp only [angleEigenBasis_apply]
  exact angleEigenPolynomial_eigen hκ n

lemma angleEigenPolynomial_zero (κ : ℝ) : angleEigenPolynomial κ 0=1 := by
  exact eq_one_of_monic_natDegree_zero (angleEigenPolynomial_monic κ 0)
    (angleEigenPolynomial_natDegree κ 0)

end SLEExactGauge

end

end OAI
