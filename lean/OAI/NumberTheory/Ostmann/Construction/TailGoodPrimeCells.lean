import OAI.NumberTheory.Ostmann.Construction.CollisionCellChoice
import OAI.NumberTheory.Ostmann.Preliminaries.StableSummandTails

namespace OAI

/-! # Nearby balanced cells for the actual summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def tailCellExceptionalPrimes (A B : Set ℕ) (N lo hi Q : ℕ) : Finset ℕ :=
  collisionExceptionalPrimes (Nat.primesLE Q) (tailSupport A N)
    (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass (summandTail A lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p)
    (fun p => fiberMass (summandTail B lo hi)
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p))

theorem EventuallyPrimeSumset.tail_good_prime_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∃ H : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ target : ℝ, H ≤ target →
      target + 64 * tailDefectBudget a C L + 2 ≤ Real.log (tailCollisionCutoff L : ℝ) →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C L + 1 ∧
        1 / (4 * ((j : ℝ) + 1)) ≤
          ∑ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
            (p : ℝ)⁻¹ ∧
        (∀ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
            ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨H, hchoose⟩ := P0.collision_cell_near
  refine ⟨a, ha, H, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let Q := tailCollisionCutoff L
  let P := Nat.primesLE Q
  let S := tailSupport A N
  let T := fun p => Finset.range p \ tailSupport A N p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff L) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff L) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff L) hi).card : ℝ)) (negativeResidue p)
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE hp
  have hS : ∀ p ∈ P, (S p).Nonempty := fun p hp =>
    tailSupport_nonempty hA N p (hprime p hp).pos
  have hT : ∀ p ∈ P, (T p).Nonempty := fun p hp =>
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard : ∀ p ∈ P, (S p).card + (T p).card = p :=
    fun p _ => tailSupport_card_add_complement A N p
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ tailDefectBudget a C L := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
      ha hcut.1 hcut.2.1 hhi hcut.2.2
      (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM
  have hE : 0 ≤ tailDefectBudget a C L := le_trans
    (Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp).le)) hbudget
  intro target htarget hupper
  have hQ1 := (tailCollisionCutoff_bounds L hcut.1 hcut.2.1).1
  apply hchoose P S T μ ν (tailDefectBudget a C L) target hE htarget
    hprime hS hT hcard hbudget
  intro j hjlo hjhi p hp
  obtain ⟨hpprime, _, hplog⟩ := mem_primeLogCellSet_iff.mp hp
  have hlog : Real.log (p : ℝ) ≤ Real.log (Q : ℝ) := by
    change Real.log (p : ℝ) ≤ Real.log (tailCollisionCutoff L : ℝ)
    linarith [hplog.2]
  have hpQ : (p : ℝ) ≤ Q :=
    (Real.log_le_log_iff (by exact_mod_cast hpprime.pos)
      (by exact_mod_cast hQ1)).mp hlog
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpQ, hpprime⟩

theorem EventuallyPrimeSumset.tail_good_prime_cells
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧ ∃ H : ℝ, ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ target : ℝ, H ≤ target →
      target + 64 * tailDefectBudget a C L + 2 ≤ Real.log (tailCollisionCutoff L : ℝ) →
      ∃ j : ℕ, target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C L + 1 ∧
        1 / (4 * ((j : ℝ) + 1)) ≤
          ∑ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
            (p : ℝ)⁻¹ ∧
        (∀ p ∈ primeLogCellSet 1 0 j ((j : ℝ) + 1) \
            tailCellExceptionalPrimes A B N (summandTailCutoff L) hi (tailCollisionCutoff L),
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
            ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hrest⟩ := h.tail_good_prime_cells_at P0 hsize hA hB N hN C hM
  exact ⟨N, a, ha, hrest⟩

end Ostmann

end OAI
