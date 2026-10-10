import OAI.NumberTheory.Ostmann.Construction.BiasedTailSelection
import OAI.NumberTheory.Ostmann.Preliminaries.UniformTailStability
import OAI.NumberTheory.Ostmann.ZeroDensity.TailDensityMask

namespace OAI

/-! # Stable biased primes for the actual large summand tails -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def tailDefectBudget (a C L : ℝ) : ℝ :=
  20 * Real.log L + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a

theorem exists_eventual_stable_summand_tails_at (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) hi).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) hi).card ∧
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE (tailCollisionCutoff L) →
      (∀ p ∈ P, p ≠ 2) → ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (t : ℕ → ℤ),
      (∀ p ∈ P, δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) →
      ∃ ε : ℕ → ℝ,
        (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * tailDefectBudget a C L / δ ^ 2 ≤
          ∑ p ∈ stableTailPrimes A B N (summandTailCutoff L) hi P δ, Real.log (p : ℝ) / p ∧
        ∀ p ∈ stableTailPrimes A B N (summandTailCutoff L) hi P δ,
          (ε p = 1 ∨ ε p = -1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
          (positiveSummandTail A (summandTailCutoff L) hi).card * (δ / 4) ≤
            ∑ n ∈ positiveSummandTail A (summandTailCutoff L) hi, orientedQuadraticValue ε t n p ∧
          (negativeSummandTail B (summandTailCutoff L) hi).card * (δ / 4) ≤
            ∑ n ∈ negativeSummandTail B (summandTailCutoff L) hi, orientedQuadraticValue (fun p => -ε p) t n p := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨a, ha, ?_⟩
  filter_upwards [hlarge, eventual_tailCollisionCutoff N] with L hlarge hcut
  intro hi hhi
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  refine ⟨hsa, hsb, ?_⟩
  intro P hPsub hodd δ hδ hδU t hbias
  let lo := summandTailCutoff L
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primesLE (hPsub hp)
  have hlo (p : ℕ) (hp : p ∈ P) : N + p ≤ lo :=
    (Nat.add_le_add_left (Nat.le_of_mem_primesLE (hPsub hp)) N).trans hcut.2.2
  have hLp : 0 < L := by linarith [hcut.1]
  have hsa' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
    simpa only [positiveSummandTail_card] using hsa
  have hsb' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B lo hi).card := by
    simpa only [negativeSummandTail_card] using hsb
  have hA₀ : (summandTail A lo hi).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < (summandTail A lo hi).card := (by positivity : 0 < a * Real.exp (L / 2) / L ^ 3).trans_le hsa'
    exact_mod_cast hp
  have hB₀ : (summandTail B lo hi).Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < (summandTail B lo hi).card := (by positivity : 0 < a * Real.exp (L / 2) / L ^ 3).trans_le hsb'
    exact_mod_cast hp
  have hbudgetAll := uniform_tail_collision_bound hA hB N lo hi a L C ha hcut.1 hcut.2.1
    hhi hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) hsa' hsb' hM
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ tailDefectBudget a C L := by
    apply le_trans _ hbudgetAll
    apply Finset.sum_le_sum_of_subset_of_nonneg hPsub
    intro p hp _
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  exact stable_tail_quadratic_bias hA hB N lo hi P δ (tailDefectBudget a C L)
    hδ hδU hP hodd (fun p hp => hN p (hP p hp)) hlo hA₀ hB₀ t hbias hbudget

end Ostmann

end OAI
