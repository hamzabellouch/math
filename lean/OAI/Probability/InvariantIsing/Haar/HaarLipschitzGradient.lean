import OAI.Probability.InvariantIsing.Haar.HaarFrobeniusGeometry
import OAI.Probability.InvariantIsing.Haar.SpecialSkewRotation
import OAI.Probability.InvariantIsing.Haar.DerivativeComparison
import OAI.Probability.InvariantIsing.Haar.HaarFunctionalCurvature
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurvature

namespace OAI

/-! A Frobenius-Lipschitz polynomial has dimension-free carré-du-champ control. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

theorem haarPolynomial_direction_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    |matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
      (matrixPolynomialDerivation A p)| ≤ L*‖A‖ := by
  have hf := hasDerivAt_specialSkewRotation_polynomial p A hA U
  have hg := hasDerivAt_specialSkewRotation A hA U
  have hh := norm_derivative_le_of_increment_bound hf hg (fun t => by
    simpa only [specialSkewRotation_zero,one_mul,Real.norm_eq_abs,← frobeniusDistance_eq_norm,
      haarPolynomialValue]
      using hp (specialSkewRotation A hA t*U) U)
  simpa only [Real.norm_eq_abs,frobenius_norm_mul_orthogonal] using hh

theorem haarPolynomial_gamma_le_lipschitz {N : ℕ} (p : MatrixPolynomial N)
    (L : ℝ) (hL : 0 ≤ L)
    (hp : ∀ U V, |haarPolynomialValue p U-haarPolynomialValue p V| ≤
      L*frobeniusDistance U V) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarPolynomialGamma p p) U ≤ 4*L^2 := by
  let ell := matrixPolynomialDifferential p (U : Matrix (Fin N) (Fin N) ℝ)
  let A := planeFunctionalMatrix ell
  have hA : A.transpose = -A := planeFunctionalMatrix_skew ell
  have hrepr := plane_functional_representation ell A hA
  have hsq : ‖A‖^2 = haarPolynomialValue (haarPolynomialGamma p p) U := by
    rw [frobenius_norm_sq,matrixFrobeniusPair_self]
    simp only [A,planeFunctionalMatrix,haarPolynomialValue,haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  have he : ‖A‖^2 = 2*ell A := by
    rw [frobenius_norm_sq]
    exact hrepr
  have hd : |ell A| ≤ L*‖A‖ := haarPolynomial_direction_le_lipschitz p L hp U A hA
  have hn : ‖A‖ ≤ 2*L := by nlinarith [norm_nonneg A,le_abs_self (ell A)]
  rw [← hsq]
  nlinarith [norm_nonneg A]

end InvariantIsing

end

end OAI
