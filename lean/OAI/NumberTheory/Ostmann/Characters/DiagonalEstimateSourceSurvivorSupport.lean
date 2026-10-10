import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourcePivotCoprime
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem sourceHistoryTerm_surviving_pairwise
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ)→State k (l+1)→ℤ)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j→PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (ht : sourceHistoryTerm w j hj B V y P f h≠0) :
    Pairwise (fun i v=>(Sum.elim f y i).val.Coprime (Sum.elim f y v).val) := by
  exact Template.OneSidedPhase.unitHistoryTerm_surviving_pairwise k j hj
    (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] y P f h ht

theorem sourceHistoryTerm_surviving_support
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ)→State k (l+1)→ℤ)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j→PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (ht : sourceHistoryTerm w j hj B V y P f h≠0) :
    Pairwise (fun i v=>(Sum.elim f y i).val.Coprime (Sum.elim f y v).val) ∧
      ∀i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)),
        (Sum.elim f y i).val.Coprime P :=
  ⟨sourceHistoryTerm_surviving_pairwise w j hj B V y P f h ht,
    sourceHistoryTerm_surviving_pivot_coprime w j hj B V y P f h ht⟩

end Ostmann.Characters.DiagonalEstimate

end

end OAI
