import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateHistoryRatioBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateActualPivotFactors
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSampleUnits

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem unitHistoryTerm_surviving_pivot_coprime (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (S : List Bool→Finset ℤ) (path : List Bool)
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo Q) (P : ℕ+)
    (f : CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (h : SupportedHistory S j path)
    (ht : unitHistoryTerm k j hj width ζ χ a B V extra mask X Δ W S path y P f h≠0) :
    ∀i : SurvivingPrimeIndex k j width,(Sum.elim f y i).val.Coprime P := by
  have hs := RetainedRow.term_current_support k j B V extra mask X Δ W P _ _ h.val _ ht
  intro i
  cases i with
  | inl i => exact copiedSample_pivot_coprime hj width hs i
  | inr i => exact outsideSample_pivot_coprime hj width hs i

theorem sourceHistoryTerm_surviving_pivot_coprime
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ)→State k (l+1)→ℤ)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j→PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (ht : sourceHistoryTerm w j hj B V y P f h≠0) :
    ∀i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)),
      (Sum.elim f y i).val.Coprime P := by
  exact unitHistoryTerm_surviving_pivot_coprime k j hj
    (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] y P f h ht

theorem sourceHistoryTerm_surviving_pivot_ne_zero
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ)→State k (l+1)→ℤ)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j→PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (ht : sourceHistoryTerm w j hj B V y P f h≠0)
    (i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))) :
    (P:ZMod (Sum.elim f y i).val)≠0 := by
  have hc := sourceHistoryTerm_surviving_pivot_coprime w j hj B V y P f h ht i
  intro hz
  exact ((primeUpTo_prime _).coprime_iff_not_dvd.mp hc) ((ZMod.natCast_eq_zero_iff _ _).mp hz)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
