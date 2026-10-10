import OAI.NumberTheory.JointDickman.Arithmetic.CandidateExceptionalPrimes
import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset
import OAI.NumberTheory.JointDickman.Probability.CandidateRootKernel

namespace OAI

/-! # Forced hits at an independently sampled third endpoint -/

namespace JointDickman
open Finset

open Classical in
theorem independent_subset_intersects_bound {α : Type*} [DecidableEq α]
    (P Q : Finset α) (q : α → ℝ) (hQ : Q ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if ∃ p ∈ Q, p ∈ S then bernoulliSubsetMass P q S else 0) ≤
      ∑ p ∈ Q, q p := by
  have hpoint (S : Finset α) (hS : S ∈ P.powerset) :
      (if ∃ p ∈ Q, p ∈ S then bernoulliSubsetMass P q S else 0) ≤
        ∑ p ∈ Q, if p ∈ S then bernoulliSubsetMass P q S else 0 := by
    have hm := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    by_cases hh : ∃ p ∈ Q, p ∈ S
    · obtain ⟨p,hpQ,hpS⟩ := hh
      rw [ite_eq_left ⟨p,hpQ,hpS⟩]
      calc
        _ = (if p ∈ S then bernoulliSubsetMass P q S else 0) := by rw [ite_eq_left hpS]
        _ ≤ _ := single_le_sum (f := fun r => if r ∈ S then bernoulliSubsetMass P q S else 0)
          (fun r _ => by split_ifs <;> first | exact hm | exact le_rfl) hpQ
    · rw [ite_eq_right hh]
      exact sum_nonneg (fun p _ => by split_ifs; exact hm; rfl)
  calc
    _ ≤ ∑ S ∈ P.powerset, ∑ p ∈ Q, if p ∈ S then bernoulliSubsetMass P q S else 0 :=
      sum_le_sum hpoint
    _ = ∑ p ∈ Q, ∑ S ∈ P.powerset, if p ∈ S then bernoulliSubsetMass P q S else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      simpa only [singleton_subset_iff,prod_singleton] using
        bernoulliSubsetMass_required P {p} q (singleton_subset_iff.mpr (hQ hp))

open Classical in
noncomputable def candidateForcedPrimes {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (s : Fin M) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => p ∣ (candidateSiteValue e s).natAbs)

/-- Once a candidate's endpoints have been exposed, an independent third
site meets one of its forced primes with probability O(B/P0). -/
theorem candidate_forced_hit_bound {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    finiteExpectation (independentPrimeSetMass B) (fun R =>
      if ∃ p ∈ candidateForcedPrimes B e s, p ∈ R.val then 1 else 0) ≤
        (5*(B : ℝ))/(Real.log 2*auxiliaryCutoff B) := by
  classical
  have hsub : candidateForcedPrimes B e s ⊆ auxiliaryPrimes B := filter_subset _ _
  have hq (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
  have hhit := independent_subset_intersects_bound (auxiliaryPrimes B)
    (candidateForcedPrimes B e s) (fun p => 1/(p : ℝ)) hsub hq
  have heq : finiteExpectation (independentPrimeSetMass B) (fun R =>
      if ∃ p ∈ candidateForcedPrimes B e s, p ∈ R.val then 1 else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
        if ∃ p ∈ candidateForcedPrimes B e s, p ∈ S then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0 := by
    unfold finiteExpectation independentPrimeSetMass
    simp_rw [mul_ite,mul_one,mul_zero]
    exact sum_coe_sort (auxiliaryPrimes B).powerset
      (fun S : Finset ℕ => if ∃ p ∈ candidateForcedPrimes B e s, p ∈ S then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0)
  rw [heq]
  apply hhit.trans
  apply candidateSiteValue_prime_mass hB hT hM he s (auxiliaryCutoff B)
    (by exact_mod_cast hP) (candidateForcedPrimes B e s)
  · intro p hp
    have hh := mem_filter.mp hp
    exact (auxiliaryPrimes_prime B p hh.1).mem_primeFactors hh.2
      (Int.natAbs_ne_zero.mpr (candidateSiteValue_ne_zero hB he s))
  · intro p hp
    exact (mem_filter.mp (hsub hp)).2.le

end JointDickman

end OAI
