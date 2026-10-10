import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceSurvivorSupport
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseDefs
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPrior
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalWeights
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel
open TemplateOneSidedCancellation TemplateSupportRemoval HigherBiasSourceRoleBounds
open TemplateOneSidedSupportTransport
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

def sourcePairRoots (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) : Bool → ℤ :=
  fun b=>if b then h'.val.1 else h.val.1

def sourcePairTrees (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    Bool → HistoryReconstruction.Tree j := fun b=>if b then h'.val.2 else h.val.2

def sourcePairPermutations (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)) :
    Bool → Equiv.Perm (ActualCopied w.configuration (wordSize k L) j) :=
  fun b=>if b then e else Equiv.refl _

def sourceRetainedWeight (B V : (l:ℕ) → State k (l+1) → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q) : ℂ :=
  retainedHistoryWeight k B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c) j h.val.1
    (sourceState k j P
      (copiedSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L))
        (fun i=>x (.inl (e i))))
      (outsideSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L))
        (fun i=>x (.inr i)))) h.val.2

def sourcePairPolynomialGate (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) : Bool :=
  decide (∀r i,familyPolynomial (relabelFamilies
    (groupedPermutation k j (sourceWidth w.configuration (wordSize k L)) (sourcePairPermutations w j e r))
    (actualFamilies k (survivingWidth k j (sourceWidth w.configuration (wordSize k L))) j (origins k j)
      (sourcePairRoots j h h' r)
      (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P (Equiv.refl _))
      (sourcePairTrees j h h' r))) i)

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
