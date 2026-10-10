import OAI.NumberTheory.Ostmann.Supply.CollisionLogImbalance
import OAI.NumberTheory.Ostmann.Preliminaries.StableSummandTails

namespace OAI

/-! # Logarithmic imbalance for the actual large summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_logarithmic_imbalance_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE (tailCollisionCutoff L) →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
          4 * tailDefectBudget a C L * primeReciprocalLogConstant C := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨N, hN, a, ha, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi P hP
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let Q := tailCollisionCutoff L
  let S := tailSupport A N
  let T := fun p => Finset.range p \ tailSupport A N p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff L) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff L) hi).card : ℝ)) (negativeResidue p)
  have hprime (p) (hp : p ∈ Nat.primesLE Q) := Nat.prime_of_mem_primesLE hp
  have hS (p) (hp : p ∈ Nat.primesLE Q) : (S p).Nonempty :=
    tailSupport_nonempty hA N p (hprime p hp).pos
  have hT (p) (hp : p ∈ Nat.primesLE Q) : (T p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p) : (S p).card + (T p).card = p := tailSupport_card_add_complement A N p
  have hb : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
      ha hcut.1 hcut.2.1 hhi hcut.2.2
      (fun p hp => hN p (hprime p hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM.lower
  have hbP : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply le_trans _ hb
    apply Finset.sum_le_sum_of_subset_of_nonneg hP
    intro p hp _
    exact mul_nonneg (Real.log_natCast_nonneg p)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p).le)
  exact collision_logarithmic_imbalance hM Q P hP S T μ ν
    (fun p hp => hS p (hP hp)) (fun p hp => hT p (hP hp))
    (fun p _ => hcard p) (tailDefectBudget a C L) hbP

theorem EventuallyPrimeSumset.tail_logarithmic_imbalance
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE (tailCollisionCutoff L) →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
          4 * tailDefectBudget a C L * primeReciprocalLogConstant C := by
  obtain ⟨N, _, a, ha, hb⟩ := h.tail_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  exact ⟨N, a, ha, hb⟩

end Ostmann

end OAI
