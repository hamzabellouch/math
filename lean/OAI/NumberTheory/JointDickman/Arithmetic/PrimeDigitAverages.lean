import OAI.NumberTheory.JointDickman.Probability.ArithmeticCandidateKernel
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitCRT

namespace OAI

/-! # Averaging the adaptive coefficient exceptions over prime digits -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem uniformZModMass_sum (p : ℕ) [NeZero p] :
    (∑ _ : ZMod p, (1 : ℝ)/p) = 1 := by
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

theorem primeDigitMass_sum (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val] :
    (∑ r, primeDigitMass B r) = 1 :=
  finiteProductMass_sum _ (fun p => uniformZModMass_sum p.val)

noncomputable def residuePrimePatterns {B M : ℕ}
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : BlockPrimePatterns B M :=
  fun p => blockPrimeHit M p.val (r p)

theorem residuePrimePatterns_arithmetic (B M u : ℕ) :
    residuePrimePatterns (M := M) (arithmeticFirstDigits B u) = arithmeticPrimePatterns B M u := by
  funext p
  let : NeZero p.val := ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  simp only [residuePrimePatterns,arithmeticFirstDigits,primeDigits_first,arithmeticPrimePatterns]

theorem prime_square_crt_average (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (F : (∀ p : auxiliaryPrimes B, ZMod p.val) →
      (∀ p : auxiliaryPrimes B, ZMod p.val) → ℝ) :
    (∑ u ∈ range (∏ p ∈ auxiliaryPrimes B, p^2),
      F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u)) /
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2) =
      finiteExpectation (primeDigitMass B)
        (fun r => finiteExpectation (primeDigitMass B) (F r)) := by
  trans (∑ r, ∑ t, F r t)/(∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2)
  · exact prime_square_crt_digits (auxiliaryPrimes B) (auxiliaryPrimes_prime B) F
  · have hw (r : ∀ p : auxiliaryPrimes B, ZMod p.val) :
        primeDigitMass B r = 1/(∏ p ∈ auxiliaryPrimes B, (p : ℝ)) := by
      simp only [primeDigitMass,finiteProductMass,prod_div_distrib,prod_const_one]
      rw [(auxiliaryPrimes B).prod_coe_sort]
    have hsq : (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2) =
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ))^2 := prod_pow _ _ _
    simp only [finiteExpectation,hw,hsq]
    simp_rw [mul_sum,one_div_mul_eq_div,div_div]
    rw [sum_div]
    apply sum_congr rfl
    intro r _
    rw [sum_div]
    congr 1
    funext t
    ring
/-- The exposed observations may determine the entire candidate family. -/
theorem primeDigit_conditional_bound {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (F : BlockPrimePatterns B M → (∀ p : auxiliaryPrimes B, ZMod p.val) → ℝ)
    {K : ℝ} (hF : ∀ H, finiteExpectation (conditionalResidueMass H) (F H) ≤ K) :
    finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r) r) ≤ K := by
  let a := fun p : auxiliaryPrimes B => uniformImageMass (blockPrimeHit M p.val)
  have ha (p : auxiliaryPrimes B) : (∑ H, a p H) = 1 := by
    simp only [a,uniformImageMass_eq_push,finitePushMass_sum]
    simpa only [ZMod.card] using uniformZModMass_sum p.val
  have han : ∀ H, 0 ≤ finiteProductMass a H := by
    apply finiteProductMass_nonneg
    intro p H
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd := total_uniform_product_disintegration
    (fun p : auxiliaryPrimes B => blockPrimeHit M p.val) F
  simp only [ZMod.card] at hd
  change finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r) r) =
    finiteExpectation (finiteProductMass a)
      (fun H => finiteExpectation (conditionalResidueMass H) (F H)) at hd
  rw [hd]
  exact (finiteExpectation_mono _ han hF).trans_eq
    (finiteExpectation_const _ (finiteProductMass_sum a ha) K)

theorem adaptive_masked_coefficient_probability {B L T H M N : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (I : BlockPrimePatterns B M → Finset (BlockCandidateIndex M))
    (he : ∀ S e, e ∈ I S → BlockCandidateAdmissible B L T H τ C e)
    (hcard : ∀ S, (I S).card ≤ N) :
    finiteProbability (primeDigitMass B) (fun r =>
      MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r) ≤
      24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  rw [finiteProbability_eq_indicator_mean]
  apply primeDigit_conditional_bound (fun S r => if MaskedCoefficientEvent (I S) S r then 1 else 0)
  intro S
  have h := masked_coefficient_event_bound hB hT hM hP (I S) (he S) hsize hhalf S
  rw [finiteProbability_eq_indicator_mean] at h
  exact h.trans (by gcongr; exact_mod_cast hcard S)

theorem adaptive_coefficient_digit_probability {B L T H M N : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (I : (∀ p : auxiliaryPrimes B, ZMod p.val) → Finset (BlockCandidateIndex M))
    (he : ∀ r e, e ∈ I r → BlockCandidateAdmissible B L T H τ C e)
    (hcard : ∀ r, (I r).card ≤ N) :
    finiteExpectation (primeDigitMass B) (fun r =>
      finiteProbability (primeDigitMass B) (CoefficientDigitEvent B (I r) r)) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hpoint r := (coefficient_digit_event_bound hB hT hM hP (I r) (he r) r).trans
    (show 12*((I r).card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) by
        gcongr; exact_mod_cast hcard r)
  exact (finiteExpectation_mono _ (primeDigitMass_nonneg B) hpoint).trans_eq
    (finiteExpectation_const _ (primeDigitMass_sum B) _)

end JointDickman

end OAI
