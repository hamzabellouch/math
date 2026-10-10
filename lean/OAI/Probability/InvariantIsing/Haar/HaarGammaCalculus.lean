import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma

namespace OAI

/-! First-order product and square-gradient identities for the rotation carré du champ. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialGamma_mul {N : ℕ} (p q r : MatrixPolynomial N) :
    haarPolynomialGamma p (q*r) = q*haarPolynomialGamma p r+r*haarPolynomialGamma p q := by
  simp only [haarPolynomialGamma,Derivation.leibniz,smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma haarPolynomialGamma_sq {N : ℕ} (p q : MatrixPolynomial N) :
    haarPolynomialGamma p (q^2) = 2*q*haarPolynomialGamma p q := by
  rw [pow_two,haarPolynomialGamma_mul]
  ring

lemma haarPolynomialGamma_sub {N : ℕ} (p q r : MatrixPolynomial N) :
    haarPolynomialGamma p (q-r) = haarPolynomialGamma p q-haarPolynomialGamma p r := by
  simp only [haarPolynomialGamma,map_sub,mul_sub,Finset.sum_sub_distrib]

lemma haarPolynomialGamma_smul {N : ℕ} (p q : MatrixPolynomial N) (c : ℝ) :
    haarPolynomialGamma p (c • q) = c • haarPolynomialGamma p q := by
  simp only [haarPolynomialGamma,Derivation.map_smul_of_tower,mul_smul_comm,
    Finset.smul_sum]

lemma haarPolynomialDerivation_gamma_sq {N : ℕ} (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialDerivation A (haarPolynomialGamma p p) =
      ∑ i, ∑ j, 2*(matrixPolynomialDerivation (planeGenerator i j) p*
        matrixPolynomialDerivation A (matrixPolynomialDerivation (planeGenerator i j) p)) := by
  simp only [haarPolynomialGamma,map_sum,Derivation.leibniz,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end InvariantIsing

end

end OAI
