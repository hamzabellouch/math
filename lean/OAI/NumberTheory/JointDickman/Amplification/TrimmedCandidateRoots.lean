import OAI.NumberTheory.JointDickman.Arithmetic.CandidateCoefficientPrimes

namespace OAI

/-! # Exact arithmetic identification after removing coefficient tests -/

namespace JointDickman
open Finset Classical

noncomputable def arithmeticCandidateHit {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) (m : BlockCandidateIndex M → ℕ) : I.powerset :=
  ⟨I.filter (fun e => p ∣ m e),mem_powerset.mpr (filter_subset _ _)⟩

noncomputable def trimmedCandidatePrimeHit {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (p : ℕ) [Fact p.Prime]
    (H : (univ : Finset (Fin M)).powerset) (r : ZMod p) : I.powerset :=
  ⟨(maskedCandidatePrimeHit I p H r).val.filter (fun e => p ∉ candidateCoefficientPrimes B e),
    mem_powerset.mpr ((filter_subset _ _).trans (mem_powerset.mp (maskedCandidatePrimeHit I p H r).property))⟩

/-- The finite exclusions used here are explicit arithmetic events. Outside
them, the original quotient prime sets equal the trimmed residue model. -/
theorem arithmetic_candidate_hit_eq_trimmed {B L T H M p u : ℕ} {τ C : ℝ}
    [Fact p.Prime] (I : Finset (BlockCandidateIndex M))
    (m : BlockCandidateIndex M → ℕ) (hp : p ∈ auxiliaryPrimes B)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hforce : ∀ e ∈ I, ¬ CandidateForcedWitness B e
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hcoeff : ∀ e ∈ I, p ∈ candidateCoefficientPrimes B e → ¬ p ∣ m e) :
    arithmeticCandidateHit I p m = trimmedCandidatePrimeHit B I p
      (blockPrimeHit M p (u : ZMod p)) (u : ZMod p) := by
  apply Subtype.ext
  ext e
  by_cases hei : e ∈ I
  · by_cases hc : p ∈ candidateCoefficientPrimes B e
    · have hn := hcoeff e hei hc
      simp [arithmeticCandidateHit,trimmedCandidatePrimeHit,hei,hc,hn]
    · have hn : ¬ p ∣ candidateLow e ∧ ¬ p ∣ candidateHigh e ∧ ¬ p ∣ candidateQuotient e := by
        have hh : ¬ (p ∣ candidateLow e ∨ p ∣ candidateHigh e ∨ p ∣ candidateQuotient e) :=
          fun h => hc ((mem_candidateCoefficientPrimes e).mpr ⟨hp,h⟩)
        tauto
      have hr := arithmetic_quotient_masked_hit I hei (he e hei) hp (heq e hei)
        hn.2.1 hn.1 hn.2.2 (hforce e hei)
      simpa only [arithmeticCandidateHit,trimmedCandidatePrimeHit,mem_filter,hei,true_and,
        hc,not_false_eq_true,and_true] using hr
  · have hm : e ∉ (maskedCandidatePrimeHit I p (blockPrimeHit M p (u : ZMod p))
        (u : ZMod p)).val := fun h => hei (mem_powerset.mp
          (maskedCandidatePrimeHit I p (blockPrimeHit M p (u : ZMod p)) (u : ZMod p)).property h)
    simp [arithmeticCandidateHit,trimmedCandidatePrimeHit,hei,hm]

end JointDickman

end OAI
