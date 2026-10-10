import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDisintegrationSum

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

def sourceSurvivorCoordinatePrior : SurvivingPrimeIndex k j
    (sourceWidth w.configuration (wordSize k ℓ))→FinitePrior (PrimeUpTo s.locations.Q) :=
  Sum.elim
    (fun i=>primeShellPrior (sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k ℓ)) i))
      (sourceScheduledShells_pos w j _))
    (fun i=>primeShellPrior (sourceScheduledShells w j
      (outsideConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k ℓ)) i))
      (sourceScheduledShells_pos w j _))

def sourceSurvivorPrior := productPrior (sourceSurvivorCoordinatePrior w j)

def sourceDiagonalAmplitude (B V : (l:ℕ)→State k (l+1)→ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k ℓ) j))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q) : ℂ :=
  sourcePairAmplitude w.configuration (wordSize k ℓ) j B V
    (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k ℓ) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k ℓ) (configurationProductWidth k c)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k ℓ) j)
    (gapSchedule BD k ℓ (j+1)) P e h.val h'.val x

def sourceDiagonalKernel (hj : j<k) (B V : (l:ℕ)→State k (l+1)→ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k ℓ) j))
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) j)
    (L S : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ)))
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q) : ℂ :=
  sourceMaskedRetainedPairAt w.configuration (wordSize k ℓ) j hj (Equiv.refl _) e.symm
    (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
    (counterpartSourceMask (fun i=>sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k ℓ)) i)) e)
    x L S (x L) (x S) P h.val.1 h.val.2 h'.val.2 *
    sourceDiagonalAmplitude w j B V P e h h' x

theorem sourceSurvivorPrior_cmean
    (F : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)→ℂ) :
    (sourceSurvivorPrior w j).cmean F =
      (outsidePrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k ℓ))
        (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).cmean (fun y=>
      (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k ℓ))
        (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).cmean (fun f=>F (Sum.elim f y))) :=
  productPrior_sum_cmean _ _ F

end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
