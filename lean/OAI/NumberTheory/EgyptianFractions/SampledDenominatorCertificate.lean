import OAI.NumberTheory.EgyptianFractions.SampledResidueDenominator
import OAI.NumberTheory.EgyptianFractions.ResidueDenominatorCertificate

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.RandomProducts

/-- An unconditional arithmetic certificate in the actual sample coordinates.
The prime pool and deterministic injective vector are chosen first. Every
subsequent collection of the thousand Boolean sample blocks has one common
auxiliary denominator with the required window and binary factor. Thus a
Fourier-good realization can be used without resampling or identifying any
repeated product values. -/
theorem eventually_sampled_denominator_certificate :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      (∀ q ∈ widePrimePool (S ^ 100),
        Nat.Prime q ∧ S ^ 100 < (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) ∧
      ∃ p : Fin (blockLength S) → ℕ,
        Function.Injective p ∧
        (∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101) ∧
        Function.Injective (ResidueConstruction.subsetEntry p) ∧
        ∀ f : Fin 1000 → ((Fin (blockLength S) × Bool) → widePrimePool (S ^ 100)),
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (204204 * S) ∧
            2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
            (∀ I : Fin (blockLength S) → Fin 2,
              ResidueConstruction.subsetEntry p I ∣ M ∧
                1 ≤ ResidueConstruction.subsetEntry p I ∧
                (ResidueConstruction.subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (blockLength S) → Bool),
              sampledProduct (f i) I ∣ M ∧ 1 ≤ sampledProduct (f i) I ∧
                (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [ResidueConstruction.eventually_residue_denominator_certificate,
    eventually_residue_prime_pool_spec] with S hcert hpool
  obtain ⟨p, hpInj, hp, hsubset, hM⟩ := hcert
  refine ⟨hpool.1, hpool.2, p, hpInj, hp, hsubset, ?_⟩
  intro f
  have hpos : ∀ i j e, 0 < residueSamplePairs (f i) j e := by
    intro i j e
    exact (hpool.2 _ (f i (j, finTwoEquiv e)).property).1.pos
  have hupper : ∀ i j e, (residueSamplePairs (f i) j e : ℝ) ≤ S ^ 101 := by
    intro i j e
    exact (hpool.2 _ (f i (j, finTwoEquiv e)).property).2.2
  obtain ⟨M, hMl, hMu, hbin, hfixed, hpaired⟩ :=
    hM (fun i => residueSamplePairs (f i)) hpos hupper
  refine ⟨M, hMl, hMu, hbin, hfixed, ?_⟩
  intro i I
  have ht := hpaired i ((residueWordEquiv (blockLength S)).symm I)
  change ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) ∣ M ∧
    1 ≤ ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) ∧
    (ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) : ℝ) ≤ Real.exp (101 * S) at ht
  have heq := sampledProduct_residueWordEquiv_symm (f i) I
  rw [heq] at ht
  exact ht

end Problem337.RandomProducts

end

end OAI
