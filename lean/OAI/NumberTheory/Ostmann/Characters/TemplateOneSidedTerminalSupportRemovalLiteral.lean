import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalDefs

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

@[simp] theorem terminal_copiedRatio : copiedWindowRatio 0 0 1=1 := by
  norm_num [copiedWindowRatio]

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem terminalExpressions_eval_prime (σ τ : Reassignments k n (wordSize k L)) (r : Bool)
    (p : terminalSourceIndex w n→PrimeUpTo s.locations.Q) :
    evalExpressions (primeIntegerAssignment p) (terminalExpressions w n σ τ r)=
      constituentSampleState (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L))
        (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L))
          (sourceTerminalPermutation w n (if r then σ else τ)) p) := by
  exact permutedSampledExpressions_prime_eval k (n+1) _ _ p

theorem terminal_transfer_iff_sampled (B V : (l:ℕ)→State k (l+1)→ℤ)
    (hn : n+1 ≤ k) (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) (r : Bool)
    (p : terminalSourceIndex w n→PrimeUpTo s.locations.Q)
    (hp : samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L)) p) :
    TransferSupport k B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
      (n+1) (terminalRoots n h h' r)
      (evalExpressions (primeIntegerAssignment p) (terminalExpressions w n σ τ r))
      (terminalTrees n h h' r) ↔
    SampledTransferSupport k (fun u=>∏b,primeIntegerAssignment p (terminalPermutations w n σ τ r ⟨u,b⟩))
      B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) (n+1)
      (SampleOrigins.root k (n+1)) (terminalRoots n h h' r)
      (evalExpressions (primeIntegerAssignment p) (terminalExpressions w n σ τ r))
      (terminalTrees n h h' r) := by
  have he := terminalExpressions_eval_prime w n σ τ r p
  have hp' : samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L))
      (constituentAssignment (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L))
        (sourceTerminalPermutation w n (if r then σ else τ)) p) :=
    (samplePrimeSupport_comp_perm _ _ p (sourceTerminalPermutation w n (if r then σ else τ)).symm).mpr hp
  rw [he]
  exact sampled_prime_transfer_iff B V _ (n+1) hn _ _ _ _ hp'

theorem terminalStartKernel_at_prime (B V : (l:ℕ)→State k (l+1)→ℤ)
    (hn : n+1 ≤ k) (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1))
    (p : terminalSourceIndex w n→PrimeUpTo s.locations.Q) :
    terminalStartKernel w n B V σ τ h h' (primeIntegerAssignment p)=
      sourceTerminalKernel w n B V σ τ h h' p := by
  have hp := integerPrimeTest_at_prime (terminalGuardedPhase w n σ τ h h') p
  by_cases hc : samplePrimeSupport (schedule k (n+1)) (sourceWidth w.configuration (wordSize k L)) p
  · have hpair := retained_pair_eq_indicator k B V
      (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
        (initialGap BD k L) (configurationProductWidth k c)))
      s.locations.X (initialGap BD k L) (configurationProductWidth k c) 0 0 (n+1)
      (terminalRoots n h h') (fun r x=>evalExpressions x (terminalExpressions w n σ τ r))
      (terminalTrees n h h') (fun _=>1) (terminalIntegerPhase w n σ τ h h')
      (primeIntegerAssignment p)
    change _ = sourceTerminalKernel w n B V σ τ h h' p
    unfold terminalStartKernel
    simp_rw [←terminal_transfer_iff_sampled w n B V hn σ τ h h' _ p hc]
    rw [show (if ∀r,TransferSupport k B V
        (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) (n+1)
        (terminalRoots n h h' r)
        (evalExpressions (primeIntegerAssignment p) (terminalExpressions w n σ τ r))
        (terminalTrees n h h' r) then terminalMultiplier w n σ τ h h' (primeIntegerAssignment p) else 0)
      = _ from by
        convert hpair.symm using 1
        simp only [terminalMultiplier]
        split_ifs <;> rfl]
    simp only [terminal_copiedRatio,one_mul,terminalIntegerPhase,hp,terminalGuardedPhase,
      sourceTerminalKernel,ite_eq_left hc,sourceTerminalAmplitude]
    simp only [terminalExpressions_eval_prime w n σ τ,terminalRoots,terminalTrees,
      Bool.false_eq_true,ite_false,ite_true]
    ring
  · simp only [terminalStartKernel,terminalMultiplier,pairedHistoryMultiplier,terminalIntegerPhase,hp,
      terminalGuardedPhase,mul_zero,zero_mul,ite_self,
      sourceTerminalKernel,ite_eq_right hc]

theorem terminal_sourceHistoryPairMean_eq_start (B V : (l:ℕ)→State k (l+1)→ℤ)
    (hn : n+1 ≤ k) (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) (hroot : h.val.1=h'.val.1) :
    SourceTemplate.sourceHistoryPairMean w B V n σ τ h h'=
      fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
        (terminalStartKernel w n B V σ τ h h') := by
  rw [terminal_sourceHistoryPairMean_eq_integer w n B V σ τ h h' hroot]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  obtain ⟨p,hp,rfl⟩ := terminalSource_support_exists_prime w n x (Fintype.mem_piFinset.mp hx)
  rw [integerPrimeTest_at_prime,terminalStartKernel_at_prime w n B V hn]

end
end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
