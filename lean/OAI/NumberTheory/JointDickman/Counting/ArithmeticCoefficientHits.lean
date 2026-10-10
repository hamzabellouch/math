import OAI.NumberTheory.JointDickman.Counting.CoefficientDigitEvents
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitArithmetic

namespace OAI

/-! # Every arithmetic coefficient-prime hit is a controlled digit event -/

namespace JointDickman
open Finset Classical

def ArithmeticCoefficientHit {M : ℕ} (B : ℕ) (I : Finset (BlockCandidateIndex M))
    (m : BlockCandidateIndex M → ℕ) : Prop :=
  ∃ e ∈ I, ∃ p ∈ candidateCoefficientPrimes B e, p ∣ m e

noncomputable def arithmeticFirstDigits (B u : ℕ) : ∀ p : auxiliaryPrimes B, ZMod p.val :=
  fun p => (primeDigits p.val (u : ZMod (p.val^2))).1

noncomputable def arithmeticSecondDigits (B u : ℕ) : ∀ p : auxiliaryPrimes B, ZMod p.val :=
  fun p => (primeDigits p.val (u : ZMod (p.val^2))).2

theorem arithmetic_coefficient_hit_implies_digit {B L T H M u : ℕ} {τ C : ℝ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hhit : ArithmeticCoefficientHit B I m) :
    CoefficientDigitEvent B I (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
  obtain ⟨e,hei,p,hpc,hpm⟩ := hhit
  obtain ⟨hp,hl|hh|hc⟩ := (mem_candidateCoefficientPrimes e).mp hpc
  all_goals
    let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p hp⟩
    have hpcop := he e hei
  case inr.inr =>
    have hpn : ¬ p ∣ candidateLow e :=
      (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mp
        (hpcop.2.2.2.2.2.2.1.symm.coprime_dvd_left hc)
    exact False.elim (affine_quotient_no_third_coefficient (heq e hei) hpn hc hpm)
  all_goals
    have hab : p ∣ candidateLow e*candidateHigh e := by
      first | exact dvd_mul_of_dvd_left hl _ | exact dvd_mul_of_dvd_right hh _
    refine ⟨e,hei,p,hpc,?_⟩
    simp only [coefficientDigitTest,dite_eq_left hp]
    refine ⟨hab,?_⟩
    have hd : (p : ℤ)^2 ∣ (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1))-candidateLow e := by
      have hm : p^2 ∣ candidateHigh e*candidateLow e*m e := by
        simpa only [pow_two,mul_comm (candidateLow e) (candidateHigh e)] using Nat.mul_dvd_mul hab hpm
      have hm' : (p : ℤ)^2 ∣ (candidateHigh e : ℤ)*candidateLow e*m e := by exact_mod_cast hm
      have heq' : (candidateHigh e : ℤ)*candidateLow e*m e+candidateLow e =
          (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1)) := by exact_mod_cast heq e hei
      have hz : (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1))-candidateLow e =
          (candidateHigh e : ℤ)*candidateLow e*m e := by linear_combination -heq'
      rwa [hz]
    exact (prime_square_affine_digits u (candidateQuotient e) (candidateLow e) (e.1.1.val+1)).mp hd

end JointDickman

end OAI
