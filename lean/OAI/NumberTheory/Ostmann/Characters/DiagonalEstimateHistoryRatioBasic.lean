import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
open TemplateOneSidedSupportTelescoping
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

abbrev sourceHistoryTerm :=
  unitHistoryTerm k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) []

theorem sourceHistoryTerm_copied_window (hc : 0 < c)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j → PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (hf : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).mass f ≠ 0)
    (ht : sourceHistoryTerm w j hj B V y P f h ≠ 0) :
    Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
      gapSchedule BD k L (j+1)-sourceCopiedWidth k c) ≤ ((∏i,(f i).val:ℕ):ℝ) ∧
    ((∏i,(f i).val:ℕ):ℝ) ≤ Real.exp
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1)+sourceCopiedWidth k c) := by
  have hret := (mul_ne_zero_iff.mp ht).1
  exact fixedConfiguration_copied_window w hc j hj (sourceScheduledShells_pos w j)
    f hf B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w)) (P:ℤ) h.val.1
    (outsideSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)) y)
    h.val.2 hret

theorem copiedWindowRatio_eq_of_sourceHistoryTerm_ne_zero (hc : 0 < c)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j → PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (hf : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).mass f ≠ 0)
    (ht : sourceHistoryTerm w j hj B V y P f h ≠ 0) :
    copiedWindowRatio
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
      (sourceCopiedWidth k c) ((∏i,(f i).val:ℕ):ℤ) =
      ((Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1))/((∏i,(f i).val:ℕ):ℝ):ℝ):ℂ) := by
  have hw := sourceHistoryTerm_copied_window w j hj B V hc y P f h hf ht
  have hcnd : Real.exp
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))*
        Real.exp (-sourceCopiedWidth k c) ≤ (((∏i,(f i).val:ℕ):ℤ):ℝ) ∧
      (((∏i,(f i).val:ℕ):ℤ):ℝ) ≤ Real.exp
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))*
        Real.exp (sourceCopiedWidth k c) := by
    simpa only [Int.cast_natCast,←Real.exp_add,←sub_eq_add_neg] using hw
  rw [copiedWindowRatio,ite_eq_left hcnd]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast,Int.cast_natCast]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
