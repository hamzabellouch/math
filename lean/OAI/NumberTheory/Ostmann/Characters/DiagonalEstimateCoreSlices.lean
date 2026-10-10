import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalEnd
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseIdentity
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDisintegration

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template Template.OneSidedPhase HigherBiasSource
open HigherBiasSource.SourceTemplate InitialCharacterScale HigherBiasSourceWord
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : ℕ→ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (a b : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))

def sourceCorePairSlice
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (q r : PrimeUpTo s.locations.Q) : ℂ :=
  sourceMaskedRetainedPairAt w.configuration (wordSize k L) j hj (Equiv.refl _) e.symm
    (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
    (sourceSurvivorPhaseMasks w j P e) p a b q r P h.val.1 h.val.2 h'.val.2 *
      sourcePairCoreAmplitude w j B V P e h h'
        (primeIntegerAssignment (twoPrimeSample p a b q r))

theorem sourceSurvivorPairPhase_twoPrimeSample (hroot : h.val.1=h'.val.1)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (q r : PrimeUpTo s.locations.Q) :
    sourceSurvivorPairPhase w j hj P e h h' (twoPrimeSample p a b q r)=
      sourceMaskedRetainedPairAt w.configuration (wordSize k L) j hj (Equiv.refl _) e.symm
        (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
        (sourceSurvivorPhaseMasks w j P e) p a b q r P h.val.1 h.val.2 h'.val.2 := by
  have he := sourceSurvivorPairPhase_eq_masked_self w j hj P e h h' hroot a b
    (twoPrimeSample p a b q r)
  simpa only [sourceMaskedRetainedPairAt,sourceRetainedPairAt,twoPrimeSample_self] using he

theorem sourceCorePairSlice_eq (hroot : h.val.1=h'.val.1)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (q r : PrimeUpTo s.locations.Q) :
    sourceCorePairSlice w j hj B V P e h h' a b p q r=
      sourceSurvivorPairPhase w j hj P e h h' (twoPrimeSample p a b q r) *
        sourcePairCoreAmplitude w j B V P e h h'
          (primeIntegerAssignment (twoPrimeSample p a b q r)) := by
  rw [sourceSurvivorPairPhase_twoPrimeSample w j hj P e h h' a b hroot]
  rfl

theorem sourceCorePairMean_eq_two_prime_slices (hroot : h.val.1=h'.val.1) :
    sourceCorePairMean w j hj B V P e h h'=
      (sourceSurvivorPrior w j).cmean (fun p=>
        (sourceSurvivorCoordinatePrior w j a).cmean (fun q=>
          (sourceSurvivorCoordinatePrior w j b).cmean (fun r=>
            sourceCorePairSlice w j hj B V P e h h' a b p q r))) := by
  unfold sourceCorePairMean sourceSurvivorPrior
  rw [productPrior_cmean_update_two (sourceSurvivorCoordinatePrior w j) a b]
  congr 1
  funext p
  congr 1
  funext q
  congr 1
  funext r
  exact (sourceCorePairSlice_eq w j hj B V P e h h' a b hroot p q r).symm

theorem norm_sourceCorePairMean_le_of_slices (hroot : h.val.1=h'.val.1) (ε : ℝ)
    (hslice : ∀p,(sourceSurvivorPrior w j).mass p≠0 →
      ‖(sourceSurvivorCoordinatePrior w j a).cmean (fun q=>
        (sourceSurvivorCoordinatePrior w j b).cmean (fun r=>
          sourceCorePairSlice w j hj B V P e h h' a b p q r))‖ ≤ ε) :
    ‖sourceCorePairMean w j hj B V P e h h'‖ ≤ ε := by
  rw [sourceCorePairMean_eq_two_prime_slices w j hj B V P e h h' a b hroot]
  exact norm_cmean_le_of_mass_support (sourceSurvivorPrior w j) _ ε hslice

theorem norm_sourceCorePairMean_le_of_supported_slices (hroot : h.val.1=h'.val.1) (ε : ℝ)
    (hslice : ∀p,(∀i,p i∈sourceSurvivorShells w j i) →
      ‖(sourceSurvivorCoordinatePrior w j a).cmean (fun q=>
        (sourceSurvivorCoordinatePrior w j b).cmean (fun r=>
          sourceCorePairSlice w j hj B V P e h h' a b p q r))‖ ≤ ε) :
    ‖sourceCorePairMean w j hj B V P e h h'‖ ≤ ε := by
  apply norm_sourceCorePairMean_le_of_slices w j hj B V P e h h' a b hroot ε
  intro p hp
  apply hslice p
  rw [sourceSurvivorPrior_eq_product] at hp
  exact primeProductPrior_mem_of_mass_ne_zero _ (sourceSurvivorShells_pos w j) p hp

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
