import OAI.NumberTheory.JointDickman.Amplification.ArithmeticRootMask
import OAI.NumberTheory.JointDickman.Arithmetic.CandidateDefectPrimes

namespace OAI

/-! # Reciprocal mass of the exceptional coefficient primes -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCoefficientPrimes {M : ℕ} (B : ℕ)
    (e : BlockCandidateIndex M) : Finset ℕ :=
  auxiliaryDivisors B (candidateLow e : ℤ) ∪
    auxiliaryDivisors B (candidateHigh e : ℤ) ∪
    auxiliaryDivisors B (candidateQuotient e : ℤ)

theorem mem_candidateCoefficientPrimes {B M p : ℕ} (e : BlockCandidateIndex M) :
    p ∈ candidateCoefficientPrimes B e ↔ p ∈ auxiliaryPrimes B ∧
      (p ∣ candidateLow e ∨ p ∣ candidateHigh e ∨ p ∣ candidateQuotient e) := by
  simp only [candidateCoefficientPrimes,auxiliaryDivisors,mem_union,mem_filter,
    Int.natAbs_natCast]
  tauto

theorem candidateCoefficientPrimes_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) :
    (∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ)) ≤
      12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hl : (∑ p ∈ auxiliaryDivisors B (candidateLow e : ℤ), 1/(p : ℝ)) ≤
      5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    have hh := auxiliaryDivisors_mass (candidateSiteValue_ne_zero hB he e.1.1)
      (candidateSiteValue_size hB hT hM he e.1.1) hP
    simpa only [candidateSiteValue_low] using hh
  have hh : (∑ p ∈ auxiliaryDivisors B (candidateHigh e : ℤ), 1/(p : ℝ)) ≤
      5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    have hh := auxiliaryDivisors_mass (candidateSiteValue_ne_zero hB he e.1.2)
      (candidateSiteValue_size hB hT hM he e.1.2) hP
    simpa only [candidateSiteValue_high he] using hh
  have hc : (∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ)) ≤
      2*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    apply auxiliaryDivisors_mass (by exact_mod_cast he.2.2.2.1.ne') _ hP
    simpa only [Int.natAbs_natCast] using (candidate_quotient_exp_bounds he).2
  unfold candidateCoefficientPrimes
  calc
    _ ≤ ((∑ p ∈ auxiliaryDivisors B (candidateLow e : ℤ), 1/(p : ℝ))+
        ∑ p ∈ auxiliaryDivisors B (candidateHigh e : ℤ), 1/(p : ℝ))+
        ∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ) :=
      (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ)) (fun _ => by positivity)).trans
        (add_le_add (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ))
          (fun _ => by positivity)) le_rfl)
    _ ≤ 5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)+
        5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)+
        2*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := add_le_add (add_le_add hl hh) hc
    _ = _ := by ring

end JointDickman

end OAI
