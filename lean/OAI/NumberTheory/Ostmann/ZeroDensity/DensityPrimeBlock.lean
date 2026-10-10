import OAI.NumberTheory.Ostmann.Construction.BiasedPrimeBlock

namespace OAI

/-! # A populated small-prime block with balanced residue masks -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_density_prime_block {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (U C E : ℝ) (hU : 1 ≤ U)
    (hUC : 4 * (Real.log 2 + 2 * C) ≤ U) (hM : MertensEstimate C)
    (hdis : ∀ p ∈ logPrimeBand U, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hbudget : (∑ p ∈ logPrimeBand U, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ E)
    (hE : 64 * E ≤ U / 4) :
    ∃ (z : ℕ) (P : Finset ℕ), 2 ≤ z ∧ P.Nonempty ∧ P ⊆ logPrimeBand U ∧
      (∀ p ∈ P, z ≤ p ∧ p < 2 * z) ∧
      (z : ℝ) ≤ (8 + 8 / Real.log 2) * Real.log z * P.card ∧
      (∀ p ∈ P, (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
        ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)
  have hprime (p : ℕ) (hp : p ∈ logPrimeBand U) : p.Prime := (logPrimeBand_mem hp).1
  have hS : ∀ p ∈ logPrimeBand U, (S p).Nonempty := fun p hp => tailSupport_nonempty hA N p (hprime p hp).pos
  have hT : ∀ p ∈ logPrimeBand U, (T p).Nonempty := fun p hp =>
    tailSupport_complement_nonempty hB (hprime p hp).pos (hdis p hp)
  have hc : ∀ p ∈ logPrimeBand U, (S p).card + (T p).card = p := fun p _ =>
    tailSupport_card_add_complement A N p
  let R := stableTailPrimes A B N lo hi (logPrimeBand U) 1
  have hRsub : R ⊆ logPrimeBand U := Finset.filter_subset _ _
  have hw := stableBiasPrimes_weight (logPrimeBand U) S T μ ν 1 E (by norm_num) hprime hS hT
    (fun p hp => (hc p hp).le) hbudget
  change (∑ p ∈ logPrimeBand U, Real.log (p : ℝ) / p) - 64 * E / 1 ^ 2 ≤
    ∑ p ∈ R, Real.log (p : ℝ) / p at hw
  norm_num only [one_pow, div_one] at hw
  have hmass : (1 / 2 : ℝ) * U ≤ ∑ p ∈ R, Real.log (p : ℝ) / p := by
    linarith [(logPrimeBand_weight_bounds U C hU hM).1]
  obtain ⟨z, P, hz, hP, hPne, hrange, hpop⟩ := exists_populated_prime_block R
    ⌊Real.exp (2 * U)⌋₊ U (1 / 2) hU (by norm_num)
    (fun p hp => hprime p (hRsub hp))
    (fun p hp => Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp (hRsub hp)).1)
    (Nat.floor_le (Real.exp_nonneg _)) hmass
  refine ⟨z, P, hz, hPne, hP.trans hRsub, hrange, ?_, ?_⟩
  · convert hpop using 1
    ring
  · intro p hp
    have hh := stableBiasPrimes_pointwise (logPrimeBand U) S T μ ν
      (fun _ _ => 0) (fun _ _ => 0) 1 (by norm_num) (by norm_num) hS hT hc
      (fun _ _ _ _ => by norm_num) (fun _ _ _ _ => by norm_num) p (hP hp)
    exact ⟨hh.1, hh.2.1⟩

end Ostmann

end OAI
