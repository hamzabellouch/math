import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeFactorization
import OAI.NumberTheory.CubicMoment.Estimates.KummerPrimeFactorization
import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularKummerPrime

namespace OAI

/-! Exact independent-prime factorization for arbitrary numerator,
including units and powers of the ramified prime. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularPrimeSum_numerator_squarefree (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) :
    fullStructuredAngularPrimeSum ℓ R v 1 1 e u W X =
      squarefreePrimePolynomial (fullPrimeSupport R W X)
        (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 := by
  classical
  unfold fullStructuredAngularPrimeSum squarefreePrimePolynomial angularCoefficientPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  have hbp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) hb
  rw [squarefreeConvolution_mul_character]
  rw [show squarefreeConvolution (fullPrimeSupport R W X) (excludedPrimeWeight e W X) b =
      fullPrimeCoefficient R W X b*primeExclusionCharacter e b from
        squarefreeConvolution_mul_character _ _ _ b]
  rw [primeExclusionCharacter_apply,cubicNumeratorHom_primary v hbp]
  simp only [one_pow,one_mul,mul_one,zero_add]
  by_cases he : IsCoprime b e <;> simp only [he,ite_true,ite_false,mul_one,mul_zero,zero_mul]
  ring

lemma fullStructuredAngularPrimeSum_numerator_factorization (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) :
    (∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (angularKummerCharacter ℓ v) e u)-
      fullStructuredAngularPrimeSum ℓ R v 1 1 e u W X =
      twistedErrorPrimePolynomial (fullPrimeSupport R W X) (excludedPrimeWeight e W X)
        (cubicNumeratorHom v) ℓ u 0 := by
  classical
  have hp := fullPrimeProduct_sub_squarefree (fullPrimeSupport R W X)
    (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p)
    (fullPrimeSupport_prime R W X) ℓ u 0
  have he : errorPrimePolynomial (fullPrimeSupport R W X)
      (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 =
      twistedErrorPrimePolynomial (fullPrimeSupport R W X) (excludedPrimeWeight e W X)
        (cubicNumeratorHom v) ℓ u 0 := by
    unfold errorPrimePolynomial twistedErrorPrimePolynomial angularCoefficientPolynomial
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    rw [squarefreeConvolutionError,orderedConvolution_mul_character,
      squarefreeConvolution_mul_character,squarefreeConvolutionError,sub_mul]
    ring
  rw [he,← fullStructuredAngularPrimeSum_numerator_squarefree ℓ] at hp
  have hprod : fullPrimeProductPolynomial (fullPrimeSupport R W X)
      (fun i p => excludedPrimeWeight e W X i p*cubicNumeratorHom v p) ℓ u 0 =
      ∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (angularKummerCharacter ℓ v) e u := by
    unfold fullPrimeProductPolynomial
    simp only [zero_add]
    apply Finset.prod_congr rfl
    intro i _
    rw [← excluded_prime_factor_eq R W X i e (angularKummerCharacter ℓ v) u]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cubicNumeratorHom_primary v (fullPrimeSupport_prime R W X i p hp).1]
    unfold angularKummerCharacter
    ring
  rwa [hprod] at hp

end CubicFirstMoment

end

end OAI
