import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalKernels
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairLiteral

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSourceRoleBounds
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel
open TemplateOneSidedSupportTransport TemplateSupportRemoval TemplateOneSidedCancellation Template.OneSidedPhase
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j < k)

def sourcePairCoreAmplitude (B V : ℕ → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → ℤ) : ℂ :=
  survivingCorePairAmplitude k j (sourceWidth w.configuration (wordSize k L)) B V
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L)) s.J P h.val.1 h'.val.1
    (Equiv.refl _) e h.val.2 h'.val.2 (sourcePairPolynomialGate w j P e h h')
    s.locations.X (initialGap BD k L) (sourceAtomWidth k c) (configurationProductWidth k c)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c) x

theorem sourcePairExpressions_eval (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)) (r : Bool)
    (x : GroupedSourceIndex w j → ℤ) :
    evalExpressions x (sourcePairExpressions w j P e r)=
      survivingIntegerState k j (sourceWidth w.configuration (wordSize k L)) P
        (sourcePairPermutations w j e r) (ungroupSourceAssignment w j x) := by
  rw [sourcePairExpressions,groupedExpressions_relabel,groupedExpressions_eval]
  rfl

theorem sourcePairEndKernel_eq_coreAmplitude (B V : ℕ → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : GroupedSourceIndex w j → ℤ) :
    sourcePairEndKernel w j hj (fun l _=>B l) (fun l _=>V l) P e h h' x=
      sourceGroupedPairPhase w j hj P e h h' x *
        sourcePairCoreAmplitude w j B V P e h h' (ungroupSourceAssignment w j x) := by
  have hh := core_pair_fixed_gate k (fun l _=>B l) (fun l _=>V l)
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c) j (sourcePairRoots j h h')
    (fun r x=>evalExpressions x (sourcePairExpressions w j P e r)) (sourcePairTrees j h h')
    (sourceGroupedCopiedProduct w j) (sourceGroupedPairPhase w j hj P e h h') x true
    (sourcePairPolynomialGate w j P e h h')
  simp only [true_and,ite_true] at hh
  change sourcePairEndKernel w j hj (fun l _=>B l) (fun l _=>V l) P e h h' x = _ at hh
  have hranges : DiagonalEstimate.sourcePivotRanges w =
      (fun l=>pivotWindow (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) l)
        (sourceAtomWidth k c)) := rfl
  rw [hh]
  rw [hranges]
  simp only [sourcePairCoreAmplitude,survivingCorePairAmplitude,sourcePairRoots,sourcePairTrees,
    sourcePairExpressions_eval,sourcePairPermutations,Bool.false_eq_true,ite_false,ite_true,
    sourceGroupedCopiedProduct]
  split <;> simp_all only [ite_true,mul_zero]
  ring

def sourceCorePairMean (B V : ℕ → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) : ℂ :=
  (sourceSurvivorPrior w j).cmean (fun p=>sourceSurvivorPairPhase w j hj P e h h' p *
    sourcePairCoreAmplitude w j B V P e h h' (primeIntegerAssignment p))

theorem sourcePairEndKernel_fullProductMean_eq_coreAmplitude (B V : ℕ → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
      (sourcePairEndKernel w j hj (fun l _=>B l) (fun l _=>V l) P e h h')=
    sourceCorePairMean w j hj B V P e h h' := by
  unfold sourceCorePairMean
  rw [sourceSurvivorPrior_cmean_eq_grouped_integer]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  obtain ⟨p,hp,rfl⟩ := groupedSource_support_exists_prime w j x (Fintype.mem_piFinset.mp hx)
  dsimp only
  rw [sourcePairEndKernel_eq_coreAmplitude,integerPrimeTest_groupedPrimeAssignment]
  rw [sourceGroupedPairPhase,integerPrimeTest_groupedPrimeAssignment,
    ungroupSourceAssignment_groupedPrimeAssignment]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
