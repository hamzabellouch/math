import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesEdgesBasic
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalization
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateActualDisjoint
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceWord
open Preliminaries InitialCharacterScale
attribute [local instance] Classical.propDecidable

theorem actualCopiedShells_bulk {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : ActualCopied cfg m j)
    (hi : IsCopiedBulk cfg m j i) : actualCopiedShells cfg m j bulk top E i = bulk := by
  change scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j
    ⟨i.1.val,i.2⟩ = bulk
  rw [scheduledPrimeShells_word cfg m j bulk top E i.1.val hi.1 i.2]
  have he : (⟨i.2.val,by simpa only [hi.1,sourceWidth_word] using i.2.isLt⟩ : Fin (m+1)) =
      Fin.castAdd 1 ⟨i.2.val,hi.2⟩ := rfl
  rw [he,roleShells,Fin.append_left]

theorem actualCopied_mem_bulk_iff {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hwidth : 0 < s.locations.w) (j : ℕ)
    (i : ActualCopied w.configuration (wordSize k L) j) (p : PrimeUpTo s.locations.Q)
    (hp : p ∈ actualCopiedShells w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes i) :
    p ∈ s.locations.base 0 ↔ IsCopiedBulk w.configuration (wordSize k L) j i := by
  constructor
  · intro hb
    by_contra hn
    have hi : (schedule k j).role i.1.val ≠ .word ∨ wordSize k L ≤ i.2.val := by
      by_cases hw : (schedule k j).role i.1.val = .word
      · exact Or.inr (Nat.le_of_not_gt (fun ha => hn ⟨hw,ha⟩))
      · exact Or.inl hw
    have hd := fixedConfiguration_scheduled_nonbulk_disjoint w hwidth j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i) hi
    exact Finset.disjoint_left.mp hd hp hb
  · intro hi
    rw [actualCopiedShells_bulk w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes i hi] at hp
    exact hp

theorem actual_matched_prior_bulk_iff {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hwidth : 0 < s.locations.w) (j : ℕ)
    (hE : ∀i,0 < primeShellMass (actualCopiedShells w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes i))
    (f : ActualCopied w.configuration (wordSize k L) j → PrimeUpTo s.locations.Q)
    (σ : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (hf : (productPrior (fun i => primeShellPrior
      (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes i) (hE i))).mass f ≠ 0)
    (hσ : (productPrior (fun i => primeShellPrior
      (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes i) (hE i))).mass (f ∘ σ) ≠ 0)
    (i : ActualCopied w.configuration (wordSize k L) j) :
    IsCopiedBulk w.configuration (wordSize k L) j (σ i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i := by
  have hi := primeProductPrior_mem_of_mass_ne_zero _ hE f hf (σ i)
  have hsi := primeProductPrior_mem_of_mass_ne_zero _ hE (f ∘ σ) hσ i
  exact (actualCopied_mem_bulk_iff w hwidth j (σ i) (f (σ i)) hi).symm.trans
    (actualCopied_mem_bulk_iff w hwidth j i (f (σ i)) hsi)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
