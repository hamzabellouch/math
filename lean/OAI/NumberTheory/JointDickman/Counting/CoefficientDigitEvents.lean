import OAI.NumberTheory.JointDickman.Arithmetic.CandidateCoefficientPrimes
import OAI.NumberTheory.JointDickman.Amplification.DependentProductMean
import OAI.NumberTheory.JointDickman.Arithmetic.HigherPrimeDigits

namespace OAI

/-! # Exceptional coefficient tests after the endpoint digits are exposed -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def primeDigitMass (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (t : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  finiteProductMass (fun (p : auxiliaryPrimes B) (_ : ZMod p.val) => 1/(p.val : ℝ)) t

theorem primeDigitMass_nonneg (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (t : ∀ p : auxiliaryPrimes B, ZMod p.val) : 0 ≤ primeDigitMass B t :=
  finiteProductMass_nonneg _ (fun _ _ => by positivity) t

theorem prime_digit_test_bound {B : ℕ} [∀ p : auxiliaryPrimes B, NeZero p.val]
    (p : auxiliaryPrimes B) (z c : ℤ) (hc : ¬ (p.val : ℤ) ∣ c) :
    finiteProbability (primeDigitMass B) (fun t =>
      (p.val : ℤ)^2 ∣ z+(p.val : ℤ)*c*((t p).val : ℤ)) ≤ 1/(p.val : ℝ) := by
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  have hone (q : auxiliaryPrimes B) :
      (∑ _t : ZMod q.val, 1/(q.val : ℝ)) = 1 := by
    simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]
    have hq : (q.val : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q.val)
    field_simp
  let f := fun t : ZMod p.val =>
    if (p.val : ℤ)^2 ∣ z+(p.val : ℤ)*c*(t.val : ℤ) then (1 : ℝ) else 0
  have hb : finiteExpectation (fun _ : ZMod p.val => 1/(p.val : ℝ)) f ≤ 1/(p.val : ℝ) := by
    have h := prime_square_digit_probability_le z c hc
    convert h using 1
    simp only [finiteExpectation,f,mul_ite,mul_one,mul_zero,sum_div,ite_div,zero_div]
  have hh := (finiteProduct_expectation_coordinate _ hone p f).trans_le hb
  rw [finiteProbability_eq_indicator_mean]
  convert hh using 1
  apply congrArg (finiteExpectation (primeDigitMass B))
  funext t
  dsimp only [f]
  split_ifs <;> rfl

noncomputable def coefficientDigitTest {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (r t : ∀ p : auxiliaryPrimes B, ZMod p.val) (p : ℕ) : Prop :=
  if hp : p ∈ auxiliaryPrimes B then
    p ∣ candidateLow e*candidateHigh e ∧
    (p : ℤ)^2 ∣ (candidateQuotient e : ℤ)*
      ((r ⟨p,hp⟩).val+(p : ℤ)*(t ⟨p,hp⟩).val+(e.1.1.val+1))-candidateLow e
  else False

theorem coefficient_digit_single_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) {p : ℕ} (hp : p ∈ auxiliaryPrimes B) :
    finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) ≤ 1/(p : ℝ) := by
  by_cases hd : p ∣ candidateLow e*candidateHigh e
  · have hcop := he.2.2.2.2.2.2.1.mul_left he.2.2.2.2.2.2.2.1
    have hc : ¬ p ∣ candidateQuotient e :=
      (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hd)
    have hc' : ¬ (p : ℤ) ∣ (candidateQuotient e : ℤ) := by exact_mod_cast hc
    have hh := prime_digit_test_bound (B := B) ⟨p,hp⟩
      ((candidateQuotient e : ℤ)*((r ⟨p,hp⟩).val+(e.1.1.val+1))-candidateLow e)
      (candidateQuotient e) hc'
    convert hh using 1
    apply congrArg (finiteProbability (primeDigitMass B))
    funext t
    apply propext
    simp only [coefficientDigitTest,dite_eq_left hp,hd,true_and]
    ring_nf
  · have hz : finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) = 0 := by
      simp [coefficientDigitTest,hp,hd,finiteProbability]
    rw [hz]
    positivity

def CoefficientDigitEvent {M : ℕ} (B : ℕ) (I : Finset (BlockCandidateIndex M))
    (r t : ∀ p : auxiliaryPrimes B, ZMod p.val) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, coefficientDigitTest B e r t p

/-- Uniform in every exposed first-digit family and its resulting candidate
list. No independence between that list and its endpoint types is assumed. -/
theorem coefficient_digit_event_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (I : Finset (BlockCandidateIndex M))
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) :
    finiteProbability (primeDigitMass B) (CoefficientDigitEvent B I r) ≤
      12*(I.card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hw := primeDigitMass_nonneg B
  calc
    _ ≤ ∑ e ∈ I, finiteProbability (primeDigitMass B)
        (fun t => ∃ p ∈ candidateCoefficientPrimes B e, coefficientDigitTest B e r t p) :=
      finiteProbability_exists_mem _ hw I _
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e,
        finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) :=
      sum_le_sum (fun e _ => finiteProbability_exists_mem _ hw _ _)
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ) := by
      apply sum_le_sum
      intro e hei
      apply sum_le_sum
      intro p hp
      exact coefficient_digit_single_bound (he e hei) r ((mem_candidateCoefficientPrimes e).mp hp).1
    _ ≤ ∑ _e ∈ I, 12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) :=
      sum_le_sum (fun e hei => candidateCoefficientPrimes_mass hB hT hM hP (he e hei))
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

end JointDickman

end OAI
