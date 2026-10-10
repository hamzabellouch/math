import OAI.NumberTheory.JointDickman.Counting.ArithmeticCoefficientHits
import OAI.NumberTheory.JointDickman.Counting.MaskedCoefficientErrors

namespace OAI

/-! # Arithmetic root families agree outside the explicit exceptional events -/

namespace JointDickman
open Finset Classical

theorem trimmedCandidatePrimeHit_eq {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (H : (univ : Finset (Fin M)).powerset)
    (r : ZMod p)
    (hno : ∀ e ∈ I, p ∈ candidateCoefficientPrimes B e →
      e ∉ (maskedCandidatePrimeHit I p H r).val) :
    trimmedCandidatePrimeHit B I p H r = maskedCandidatePrimeHit I p H r := by
  apply Subtype.ext
  apply filter_eq_self.mpr
  intro e he
  have hei : e ∈ I := mem_powerset.mp (maskedCandidatePrimeHit I p H r).property he
  exact fun hc => hno e hei hc he

noncomputable def arithmeticCandidatePrimeFamily {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ) :
    auxiliaryPrimes B → I.powerset := fun p => arithmeticCandidateHit I p.val m

/-- All three exclusions have their own proved probability bounds. The
quotient family here is the actual family satisfying the affine equations. -/
theorem arithmetic_roots_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hforce : ∀ e ∈ I, ¬ CandidateForcedWitness B e
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hactual : ¬ ArithmeticCoefficientHit B I m)
    (hmasked : ¬ MaskedCoefficientEvent I (arithmeticPrimePatterns B M u)
      (fun p => (u : ZMod p.val))) :
    arithmeticCandidatePrimeFamily B I m =
      maskedPrimeRootFamily I (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val)) := by
  funext p
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  have hc : ∀ e ∈ I, p.val ∈ candidateCoefficientPrimes B e → ¬ p.val ∣ m e := by
    intro e hei hcoef hdiv
    exact hactual ⟨e,hei,p.val,hcoef,hdiv⟩
  have hm : ∀ e ∈ I, p.val ∈ candidateCoefficientPrimes B e →
      e ∉ (maskedCandidatePrimeHit I p.val (blockPrimeHit M p.val (u : ZMod p.val))
        (u : ZMod p.val)).val := by
    intro e hei hcoef hdiv
    apply hmasked
    refine ⟨e,hei,p.val,hcoef,?_⟩
    simpa only [maskedCoefficientTest,dite_eq_left p.property,arithmeticPrimePatterns] using hdiv
  exact (arithmetic_candidate_hit_eq_trimmed I m p.property he heq hforce hc).trans
    (trimmedCandidatePrimeHit_eq I _ _ hm)

end JointDickman

end OAI
