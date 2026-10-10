import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalSourceCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalLiteral

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale DiagonalEstimate
open HigherBiasSourceRoleBounds HistoryFrequencyLabels HistoryFrequencyBudget ParityActions SymbolicHistory
open TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel TemplateOneSidedSupportTransport
open TemplateOneSidedBudget TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem terminalExpressions_eval_integer (σ τ : Reassignments k n (wordSize k L)) (r : Bool)
    (x : terminalSourceIndex w n→ℤ) :
    evalExpressions x (terminalExpressions w n σ τ r)=
      terminalIntegerState k n (sourceWidth w.configuration (wordSize k L)) (wordSize k L)
        (by rw [sourceWidth_word]; omega) (if r then σ else τ) x :=
  paritySampledExpressions_integer_eval k n _ _ _ _ x

theorem terminalEndKernel_eq_sourceCore (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1))
    (x : terminalSourceIndex w n→ℤ) :
    terminalEndKernel w n (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
      (sourceRecurrenceV BD k L) σ τ h h' x =
    terminalIntegerPhase w n σ τ h h' x *
      sourceTerminalCoreAmplitude w n σ τ h h' (terminalPolynomialGate w n σ τ h h') x := by
  have hh := core_pair_fixed_gate k
    (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c) (sourceRecurrenceV BD k L)
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c) 0 0 (n+1)
    (terminalRoots n h h') (fun r x=>evalExpressions x (terminalExpressions w n σ τ r))
    (terminalTrees n h h') (fun _=>1) (terminalIntegerPhase w n σ τ h h') x true
    (terminalPolynomialGate w n σ τ h h')
  simp only [true_and,terminal_copiedRatio,one_mul,ite_true] at hh
  unfold terminalEndKernel
  trans (if terminalPolynomialGate w n σ τ h h' then
      terminalIntegerPhase w n σ τ h h' x *
        coreHistoryWeight k (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
          (sourceRecurrenceV BD k L) (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
          (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
            (initialGap BD k L) (configurationProductWidth k c)))
          s.locations.X (initialGap BD k L) (configurationProductWidth k c) (n+1)
          (terminalRoots n h h' false) (evalExpressions x (terminalExpressions w n σ τ false))
          (terminalTrees n h h' false) *
        conj (coreHistoryWeight k (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
          (sourceRecurrenceV BD k L) (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
          (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
            (initialGap BD k L) (configurationProductWidth k c)))
          s.locations.X (initialGap BD k L) (configurationProductWidth k c) (n+1)
          (terminalRoots n h h' true) (evalExpressions x (terminalExpressions w n σ τ true))
          (terminalTrees n h h' true)) else 0)
  · convert hh using 1
    simp only [terminalMultiplier]
  · rw [terminalExpressions_eval_integer w n σ τ false x,
      terminalExpressions_eval_integer w n σ τ true x]
    simp only [sourceTerminalCoreAmplitude,terminalCorePairAmplitude,terminalRoots,terminalTrees,
      Bool.false_eq_true,ite_false,ite_true]
    split_ifs
    · convert (show ∀z a b : ℂ,z*b*conj a=z*(conj a*b) by intros; ring)
        (terminalIntegerPhase w n σ τ h h' x) _ _ using 1
      rfl
    · simp only [mul_zero]

theorem terminalCoreMean_eq_sourceTerminalCoreMean
    (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) :
    terminalCoreMean w n (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
      (sourceRecurrenceV BD k L) σ τ h h' =
      sourceTerminalCoreMean w n σ τ h h' (fun _ _=>1) (terminalPolynomialGate w n σ τ h h') := by
  unfold terminalCoreMean sourceTerminalCoreMean
  rw [terminalSourcePrior_cmean_eq_integer]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  obtain ⟨p,hp,rfl⟩ := terminalSource_support_exists_prime w n x (Fintype.mem_piFinset.mp hx)
  rw [terminalEndKernel_eq_sourceCore,terminalIntegerPhase,integerPrimeTest_at_prime,
    integerPrimeTest_at_prime]
  simp only [terminalGuardedPhase,sourceTerminalMaskedPhase,Finset.prod_const_one,one_mul,
    ]
  rfl

end
end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
