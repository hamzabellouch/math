import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairReindexedActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalIntegerPriorBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale DiagonalEstimate
open HigherBiasSourceRoleBounds
open HistoryFrequencyLabels HistoryFrequencyBudget ParityActions SymbolicHistory
open TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel TemplateOneSidedSupportTransport
open TemplateOneSidedBudget TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

def terminalRoots (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) : Bool→ℤ :=
  fun b=>if b then h.val.1 else h'.val.1

def terminalTrees (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) :
    Bool→HistoryReconstruction.Tree (n+1) := fun b=>if b then h.val.2 else h'.val.2

def terminalPermutations (σ τ : Reassignments k n (wordSize k L)) :
    Bool→Equiv.Perm (terminalSourceIndex w n) :=
  fun b=>(sourceTerminalPermutation w n (if b then σ else τ)).symm

def terminalExpressions (σ τ : Reassignments k n (wordSize k L)) (r : Bool) :
    Expressions (ι:=terminalSourceIndex w n) k (n+1) :=
  relabelExpressions (terminalPermutations w n σ τ r)
    (sampledExpressions k (n+1) (sourceWidth w.configuration (wordSize k L)))

def terminalGuardedPhase (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1))
    (p : terminalSourceIndex w n→PrimeUpTo s.locations.Q) : ℂ :=
  if samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L)) p then
    sourceTerminalPhasePair w n σ τ p h.val.1 h.val.2 h'.val.2 else 0

def terminalIntegerPhase (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) :=
  integerPrimeTest (terminalGuardedPhase w n σ τ h h')

def terminalPolynomialGate (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) : Bool :=
  decide (∀r i,familyPolynomial (relabelFamilies (terminalPermutations w n σ τ r)
    (actualFamilies k (fun u=>sourceWidth w.configuration (wordSize k L) ((schedule k (n+1)).role u))
      (n+1) (SampleOrigins.root k (n+1)) (terminalRoots n h h' r)
      (sampledExpressions k (n+1) (sourceWidth w.configuration (wordSize k L)))
      (terminalTrees n h h' r))) i)

def terminalMultiplier (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) :=
  pairedHistoryMultiplier k
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c) 0 0 (n+1)
    (terminalRoots n h h') (fun r x=>evalExpressions x (terminalExpressions w n σ τ r))
    (terminalTrees n h h') (fun _=>1) (terminalIntegerPhase w n σ τ h h')

def terminalStartKernel (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1))
    (x : terminalSourceIndex w n→ℤ) : ℂ :=
  if ∀r,SampledTransferSupport k (fun u=>∏b,x (terminalPermutations w n σ τ r ⟨u,b⟩))
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) (n+1)
    (SampleOrigins.root k (n+1)) (terminalRoots n h h' r)
    (evalExpressions x (terminalExpressions w n σ τ r)) (terminalTrees n h h' r)
  then terminalMultiplier w n σ τ h h' x else 0

def terminalEndKernel (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1))
    (x : terminalSourceIndex w n→ℤ) : ℂ :=
  if (∀r,TransferCoreSupport k B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (n+1) (terminalRoots n h h' r) (evalExpressions x (terminalExpressions w n σ τ r))
    (terminalTrees n h h' r)) ∧ terminalPolynomialGate w n σ τ h h'=true
  then terminalMultiplier w n σ τ h h' x else 0

def terminalCoreMean (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) : ℂ :=
  fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
    (terminalEndKernel w n B V σ τ h h')

end
end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
