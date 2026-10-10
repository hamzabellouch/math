import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalKernels
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalLiteral

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

theorem sourceGroupedCopiedProduct_at_prime
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q) :
    sourceGroupedCopiedProduct w j (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p)=
      ((∏i,(p (.inl i)).val:ℕ):ℤ) := by
  simp only [sourceGroupedCopiedProduct,ungroupSourceAssignment_groupedPrimeAssignment,
    primeIntegerAssignment,Nat.cast_prod]

theorem sourceGroupedPairPhase_at_prime (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q) :
    sourceGroupedPairPhase w j hj P e h h'
      (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p)=
        sourceSurvivorPairPhase w j hj P e h h' p :=
  integerPrimeTest_groupedPrimeAssignment w j _ p

theorem sourcePairStartKernel_at_prime (B V : (l:ℕ) → State k (l+1) → ℤ) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) (hroot : h.val.1=h'.val.1)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → PrimeUpTo s.locations.Q) :
    sourcePairStartKernel w j hj B V P e h h'
      (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p)=
        cutoffSourceSurvivorKernel w j hj B V P e h h' p := by
  rw [cutoffSourceSurvivorKernel_eq_guarded_phase w j hj B V P e h h' hroot]
  by_cases hg : Pairwise (fun i v=>(p i).val.Coprime (p v).val) ∧
      pivotPrimeGuard (sourceWidth w.configuration (wordSize k L)) P p
  · have hpair := matched_surviving_retained_pair_eq_sampled hj B V
      (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
        (initialGap BD k L) (configurationProductWidth k c)))
      s.locations.X (initialGap BD k L) (configurationProductWidth k c)
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
      (sourceCopiedWidth k c) (sourcePairRoots j h h') P
      (sourceWidth w.configuration (wordSize k L)) p (sourcePairPermutations w j e)
      (sourcePairTrees j h h') (sourceGroupedCopiedProduct w j)
      (sourceGroupedPairPhase w j hj P e h h') hg.1
    dsimp only at hpair
    simp only [hg.2,true_and,sourceGroupedCopiedProduct_at_prime,sourceGroupedPairPhase_at_prime,
      sourcePairRoots,sourcePairTrees,sourcePairPermutations,Bool.false_eq_true,ite_false,ite_true,
      ] at hpair
    have heval (σ : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)) :
        evalExpressions (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p)
          (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P σ) =
        sourceState k j P
          (copiedSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L))
            (fun i=>p (.inl (σ i))))
          (outsideSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L))
            (fun i=>p (.inr i))) :=
      groupedExpressions_prime_eval k j (sourceWidth w.configuration (wordSize k L)) P σ p
    simp only [heval] at hpair
    unfold sourcePairStartKernel
    simp only [sourcePairExpressions,groupedExpressions_relabel,heval]
    convert hpair.symm using 1 <;> rfl
  · have hphase : sourceSurvivorPairPhase w j hj P e h h' p=0 := by
      simp only [sourceSurvivorPairPhase,ite_eq_right hg]
    simp only [sourcePairStartKernel,pairedHistoryMultiplier,sourceGroupedPairPhase_at_prime,
      hphase,mul_zero,zero_mul,ite_self]

theorem sourceHistoryPairMean_eq_start (B V : (l:ℕ) → State k (l+1) → ℤ) (hc : 0<c) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) (hroot : h.val.1=h'.val.1) :
    sourceHistoryPairMean w j hj B V P e h h' =
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (sourcePairStartKernel w j hj B V P e h h') := by
  rw [sourceHistoryPairMean_eq_grouped_integer w j hj B V hc]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  obtain ⟨p,hp,rfl⟩ := groupedSource_support_exists_prime w j x (Fintype.mem_piFinset.mp hx)
  dsimp only
  rw [integerPrimeTest_groupedPrimeAssignment,sourcePairStartKernel_at_prime w j hj B V P e h h' hroot]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
