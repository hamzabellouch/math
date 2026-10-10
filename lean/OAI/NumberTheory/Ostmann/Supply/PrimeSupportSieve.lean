import OAI.NumberTheory.Ostmann.Supply.PrimeSupportEnergy
import OAI.NumberTheory.Ostmann.Preliminaries.FullSummandResidues
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProof

namespace OAI

/-! # The prime-support sieve estimate for the summand-size argument -/

namespace Ostmann

open scoped Classical BigOperators

 theorem full_support_prime_energy {M : ℕ} (B : Set ℕ) (U : Finset (Fin M))
    (hU : U.Nonempty) (p : ℕ) [Fact p.Prime]
    (havoid : ∀ a ∈ U, (a.val : ZMod p) ∉ negativeOccupiedResidues B p) :
    ((occupiedResidues B p).card : ℝ) / p ≤ intervalSetReducedEnergy U 0 p := by
  have hmem : ∀ a ∈ U, ((a.val : ℤ) : ZMod p) ∈ allowedSummandResidues B p := by
    intro a ha
    simpa only [allowedSummandResidues, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Int.cast_natCast] using havoid a ha
  have hS : (allowedSummandResidues B p).Nonempty := by
    obtain ⟨a, ha⟩ := hU
    exact ⟨_, hmem a ha⟩
  have hlower := prime_support_energy_lower p U hU (fun a => (a.val : ℤ))
    (allowedSummandResidues B p) hS hmem
  have h := (occupied_to_allowed_ratio B p hS).trans hlower
  simpa only [intervalSetReducedEnergy_eq_unitFrequencyEnergy, zero_add] using h

 theorem full_support_prime_sieve {M Q : ℕ} (B : Set ℕ) (U : Finset (Fin M))
    (hU : U.Nonempty) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q)
    (havoid : ∀ p ∈ P, ∀ a ∈ U, (a.val : ZMod p) ∉ negativeOccupiedResidues B p) :
    (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / U.card := by
  calc
    _ ≤ ∑ p ∈ P, intervalSetReducedEnergy U 0 p := by
      apply Finset.sum_le_sum
      intro p hp
      let : Fact p.Prime := ⟨hP p hp⟩
      exact full_support_prime_energy B U hU p (havoid p hp)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy U 0 q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Icc.mpr ⟨(hP p hp).one_le, hPQ p hp⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg U 0 q
    _ ≤ _ := additiveSieve_probability_bound publishedAdditiveLargeSieve hM hQ U hU 0

end Ostmann

end OAI
