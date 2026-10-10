import OAI.NumberTheory.JointDickman.Amplification.ArithmeticCandidateRoots
import OAI.NumberTheory.JointDickman.Probability.MaskedResidueModel
import OAI.NumberTheory.JointDickman.Amplification.CandidateForcedEvent

namespace OAI

/-! # Matching arithmetic quotient tests with the masked residue tests -/

namespace JointDickman
open Finset Classical

theorem candidateSiteValue_low {M : ℕ} (e : BlockCandidateIndex M) :
    candidateSiteValue e e.1.1 = (candidateLow e : ℤ) := by
  simp [candidateSiteValue]

theorem candidateSiteValue_high {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    candidateSiteValue e e.1.2 = (candidateHigh e : ℤ) := by
  have hi : e.1.1.val ≤ e.1.2.val := (show e.1.1.val < e.1.2.val from he.1).le
  have hlag : (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val := by
    unfold candidateLag
    exact Int.ofNat_sub hi
  have hco : (candidateHigh e : ℤ) = candidateLow e+
      (candidateLag e : ℤ)*candidateQuotient e := by
    exact_mod_cast he.2.2.2.2.1
  rw [hlag] at hco
  exact hco.symm

/-- Away from coefficient primes, an occupied residue root would be one
of the already controlled forced hits at a third site. -/
theorem candidate_occupied_root_impossible {B L T H M p u : ℕ} {τ C : ℝ}
    [Fact p.Prime] {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) (hp : p ∈ auxiliaryPrimes B)
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e)
    (hno : ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hocc : blockPrimeHit M p (u : ZMod p) ≠ emptyBlockPrimeHit M) :
    (u : ZMod p) ≠ candidateModRoot p e := by
  intro hroot
  have hnonempty : (blockPrimeHit M p (u : ZMod p)).val.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro h
    exact hocc (Subtype.ext h)
  obtain ⟨s,hs⟩ := hnonempty
  have hsite : blockSiteRoot M p s = (u : ZMod p) := (mem_filter.mp hs).2
  have hd := candidateModRoot_site_collision e s hc (hroot.symm.trans hsite.symm)
  by_cases hslo : s = e.1.1
  · subst s
    rw [candidateSiteValue_low,Int.natAbs_natCast] at hd
    exact hb hd
  by_cases hshi : s = e.1.2
  · subst s
    rw [candidateSiteValue_high he,Int.natAbs_natCast] at hd
    exact ha hd
  apply hno
  refine ⟨s,hslo,hshi,p,mem_filter.mpr ⟨hp,hd⟩,?_⟩
  exact mem_filter.mpr ⟨hp,(blockPrimeHit_divisibility M p u s).mp hs⟩

/-- Thus every nonexceptional auxiliary prime has the same test in the
actual quotient and the masked conditional model. -/
theorem arithmetic_quotient_masked_hit {B L T H M p u m : ℕ} {τ C : ℝ}
    [Fact p.Prime] (I : Finset (BlockCandidateIndex M))
    {e : BlockCandidateIndex M} (heI : e ∈ I)
    (he : BlockCandidateAdmissible B L T H τ C e) (hp : p ∈ auxiliaryPrimes B)
    (heq : candidateHigh e*candidateLow e*m+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e)
    (hno : ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    p ∣ m ↔ e ∈ (maskedCandidatePrimeHit I p
      (blockPrimeHit M p (u : ZMod p)) (u : ZMod p)).val := by
  have hr := candidate_affine_quotient_root e heq ha hb hc
  by_cases hocc : blockPrimeHit M p (u : ZMod p) = emptyBlockPrimeHit M
  · simp only [maskedCandidatePrimeHit,hocc,ite_true,rootHitType,rootHitSet,
      mem_filter,heI,true_and]
    exact hr.trans eq_comm
  · have hn := candidate_occupied_root_impossible he hp ha hb hc hno hocc
    have hm : ¬ p ∣ m := fun h => hn (hr.mp h)
    simp [maskedCandidatePrimeHit,hocc,hm]

end JointDickman

end OAI
