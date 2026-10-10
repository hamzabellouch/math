import OAI.Probability.InvariantIsing.Haar.HaarPolynomialLaplacian

namespace OAI

/-! Product and second-order identities for the actual polynomial rotation operator. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma derivation_double_product {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (p q : A) :
    D (D (p*q)) = p*D (D q)+q*D (D p)+2*(D p*D q) := by
  simp only [Derivation.leibniz,map_add,smul_eq_mul]
  ring

def haarPolynomialGamma {N : ℕ} (p q : MatrixPolynomial N) : MatrixPolynomial N :=
  ∑ i, ∑ j, matrixPolynomialDerivation (planeGenerator i j) p*
    matrixPolynomialDerivation (planeGenerator i j) q

lemma haarPolynomialLaplacian_mul {N : ℕ} (p q : MatrixPolynomial N) :
    haarPolynomialLaplacian N (p*q) = p*haarPolynomialLaplacian N q+
      q*haarPolynomialLaplacian N p+2*haarPolynomialGamma p q := by
  simp only [haarPolynomialLaplacian_apply,derivation_double_product,
    haarPolynomialGamma,Finset.sum_add_distrib,Finset.mul_sum]

lemma haarPolynomialLaplacian_sq {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (p^2) =
      2*(p*haarPolynomialLaplacian N p+haarPolynomialGamma p p) := by
  rw [pow_two,haarPolynomialLaplacian_mul]
  ring

/-- The exact Bochner identity before the nonnegative Hessian estimate. -/
theorem haarPolynomial_bochner_identity {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (haarPolynomialGamma p p) =
      2*(haarPolynomialGamma p (haarPolynomialLaplacian N p)+
        ∑ i, ∑ j, ∑ k, ∑ l,
          (matrixPolynomialDerivation (planeGenerator k l)
            (matrixPolynomialDerivation (planeGenerator i j) p))^2) := by
  unfold haarPolynomialGamma
  simp only [map_sum]
  simp_rw [← pow_two,haarPolynomialLaplacian_sq,
    haarPolynomialLaplacian_derivation _ (planeGenerator_transpose _ _)]
  simp only [haarPolynomialGamma,pow_two,mul_add,Finset.mul_sum,Finset.sum_add_distrib]

end InvariantIsing

end

end OAI
