import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalDefs
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPriorProperties

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSourceRoleBounds
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel
open TemplateOneSidedSupportTransport TemplateSupportRemoval
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k)

def sourceGroupedPairPhase (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : GroupedSourceIndex w j → ℤ) : ℂ :=
  integerPrimeTest (sourceSurvivorPairPhase w j hj P e h h') (ungroupSourceAssignment w j x)

def sourceGroupedCopiedProduct (x : GroupedSourceIndex w j → ℤ) : ℤ :=
  ∏i,ungroupSourceAssignment w j x (.inl i)

def sourcePairExpressions (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)) (r : Bool) :
    Expressions (ι:=GroupedSourceIndex w j) k j :=
  relabelExpressions
    (groupedPermutation k j (sourceWidth w.configuration (wordSize k L)) (sourcePairPermutations w j e r))
    (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P (Equiv.refl _))

def sourcePairStartKernel (B V : (l:ℕ) → State k (l+1) → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : GroupedSourceIndex w j → ℤ) : ℂ :=
  if ∀r,SampledTransferSupport k
      (fun u=>∏b,x (groupedPermutation k j (sourceWidth w.configuration (wordSize k L))
        (sourcePairPermutations w j e r) ⟨u,b⟩))
      B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) j
      (origins k j) (sourcePairRoots j h h' r)
      (evalExpressions x (sourcePairExpressions w j P e r)) (sourcePairTrees j h h' r)
  then pairedHistoryMultiplier k
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c) j (sourcePairRoots j h h')
    (fun r x=>evalExpressions x (sourcePairExpressions w j P e r)) (sourcePairTrees j h h')
    (sourceGroupedCopiedProduct w j) (sourceGroupedPairPhase w j hj P e h h') x else 0

def sourcePairEndKernel (B V : (l:ℕ) → State k (l+1) → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : GroupedSourceIndex w j → ℤ) : ℂ :=
  if (∀r,TransferCoreSupport k B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) j
      (sourcePairRoots j h h' r) (evalExpressions x (sourcePairExpressions w j P e r))
      (sourcePairTrees j h h' r)) ∧ sourcePairPolynomialGate w j P e h h'=true
  then pairedHistoryMultiplier k
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c) j (sourcePairRoots j h h')
    (fun r x=>evalExpressions x (sourcePairExpressions w j P e r)) (sourcePairTrees j h h')
    (sourceGroupedCopiedProduct w j) (sourceGroupedPairPhase w j hj P e h h') x else 0

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
