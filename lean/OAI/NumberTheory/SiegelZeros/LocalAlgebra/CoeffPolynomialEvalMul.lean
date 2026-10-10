import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.Homogenize

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coeff_polynomial_eval₂_mul
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) (n : ℕ) :
    ((p.eval₂ (Polynomial.C.comp c)
      (fun i => Polynomial.C (x i) * Polynomial.X)).coeff n) =
        (homogeneousComponent n p).eval₂ c x := by
  classical
  have hh (i : ℕ) : (homogeneousComponent i p).eval₂ (Polynomial.C.comp c)
      (fun j => Polynomial.C (x j) * Polynomial.X) =
        Polynomial.C ((homogeneousComponent i p).eval₂ c x) * Polynomial.X ^ i := by
    rw [homogeneous_eval₂_mul (homogeneousComponent_isHomogeneous i p),
      ← MvPolynomial.hom_eval₂]
  conv_lhs => rw [← sum_homogeneousComponent p]
  simp only [eval₂_sum, Polynomial.finsetSum_coeff, hh, Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < p.totalDegree + 1
  · simp [hn]
  · have hdegree : p.totalDegree < n := by omega
    simp [hn, homogeneousComponent_eq_zero n p hdegree]

theorem polynomial_eval₂_homogeneousComponent
    {S : Type*} [CommSemiring S] (c : K →+* S) (x : σ → S)
    (p : MvPolynomial σ K) (n : ℕ) :
    (homogeneousComponent n p).eval₂ (Polynomial.C.comp c)
      (fun i => Polynomial.C (x i) * Polynomial.X) =
        Polynomial.C ((p.eval₂ (Polynomial.C.comp c)
          (fun i => Polynomial.C (x i) * Polynomial.X)).coeff n) * Polynomial.X ^ n := by
  rw [homogeneous_eval₂_mul (homogeneousComponent_isHomogeneous n p),
    ← MvPolynomial.hom_eval₂, coeff_polynomial_eval₂_mul]

end WeightedTorusJets.Geometry



end SiegelZeros

end OAI
