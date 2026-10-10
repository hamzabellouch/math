import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.ExcludedPrimeInput

namespace OAI

/-! Exact independent-prime factorization, keeping the squarefree error
and the coprimality exclusion of the actual structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeExclusionCharacter (e : Eisenstein) : Eisenstein →* ℂ :=
  (1 : MulChar (Residues e) ℂ).toMonoidHom.comp
    (Ideal.Quotient.mk (modulus e)).toMonoidHom

lemma primeExclusionCharacter_apply (e z : Eisenstein) :
    primeExclusionCharacter e z = if IsCoprime z e then 1 else 0 :=
  principal_residue_value e z

def excludedPrimeWeight (e : Eisenstein) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (i : ι) (p : Eisenstein) : ℂ := W i (norm p/X i)*primeExclusionCharacter e p

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_eq_prime_filter (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (i : ι) :
    fullPrimeSupport R W X i = (primeCutoff (R*X i)).filter (fun p => W i (norm p/X i) ≠ 0) := by
  ext p
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall,mem_primeCutoff,primaryPrime]
  tauto

omit [Fintype ι] [DecidableEq ι] in
lemma excluded_prime_factor_eq (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (i : ι) (e : Eisenstein) (χ : Eisenstein → ℂ) (u : ℝ) :
    (∑ p ∈ fullPrimeSupport R W X i,
      excludedPrimeWeight e W X i p*χ p*mellinPhase u (norm p)) =
      excludedSmoothPrimeCharacterSum R (X i) (W i) χ e u := by
  rw [fullPrimeSupport_eq_prime_filter]
  unfold excludedSmoothPrimeCharacterSum
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  unfold excludedPrimeWeight
  rw [primeExclusionCharacter_apply]
  by_cases hw : W i (norm p/X i) = 0 <;> by_cases he : IsCoprime p e <;>
    simp only [hw,he,ne_eq,not_true_eq_false,not_false_eq_true,ite_true,ite_false,
      zero_mul,mul_zero,mul_one]
  ring

lemma fullStructuredPrimeSum_eq_mixedSquarefree (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {a b : Eisenstein} (ha : primary a) (hb : primary b) (e : Eisenstein) (u : ℝ) :
    fullStructuredPrimeSum R a b 1 e u W X =
      mixedSquarefreePrimePolynomial (fullPrimeSupport R W X)
        (excludedPrimeWeight e W X) a b 0 u 0 := by
  unfold fullStructuredPrimeSum mixedSquarefreePrimePolynomial angularCoefficientPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) hz
  dsimp only
  rw [show squarefreeConvolution (fullPrimeSupport R W X) (excludedPrimeWeight e W X) z =
      fullPrimeCoefficient R W X z*primeExclusionCharacter e z from
        squarefreeConvolution_mul_character _ _ _ z,
    primeExclusionCharacter_apply,mixedCubic_numerator ha hb hp,theta_zero,zero_add,one_mul,mul_one]
  by_cases he : IsCoprime z e <;> simp only [he,ite_true,ite_false,mul_one,mul_zero,zero_mul]
  ring

lemma fullStructuredPrimeSum_factorization (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {a b : Eisenstein} (ha : primary a) (hb : primary b) (e : Eisenstein) (u : ℝ) :
    (∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (mixedCubic a b) e u)-
      fullStructuredPrimeSum R a b 1 e u W X =
      twistedErrorPrimePolynomial (fullPrimeSupport R W X)
        (excludedPrimeWeight e W X) (mixedCubic a b) 0 u 0 := by
  rw [fullStructuredPrimeSum_eq_mixedSquarefree R W X ha hb]
  have hp := fullPrimeProduct_sub_mixedSquarefree (fullPrimeSupport R W X)
    (excludedPrimeWeight e W X) (fullPrimeSupport_prime R W X) ha hb 0 u 0
  have heq : fullPrimeProductPolynomial (fullPrimeSupport R W X)
      (fun i p => excludedPrimeWeight e W X i p*mixedCubic a b p) 0 u 0 =
      ∏ i, excludedSmoothPrimeCharacterSum R (X i) (W i) (mixedCubic a b) e u := by
    unfold fullPrimeProductPolynomial
    simp only [theta_zero,mul_one,zero_add]
    exact Finset.prod_congr rfl (fun i _ => excluded_prime_factor_eq R W X i e _ u)
  rwa [heq] at hp

end CubicFirstMoment

end

end OAI
