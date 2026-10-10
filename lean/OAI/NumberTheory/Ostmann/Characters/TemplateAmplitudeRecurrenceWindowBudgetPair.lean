import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowBudgetBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds InitialCharacterScale HistoryFrequencyBudget HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

variable {d : Decomposition} {E₀ : Finset ℕ} {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
variable {s : SelectedWordSource d E₀ δ L k α β ρ γ c₀}

theorem fixedConfiguration_canonicalPairBounds_of_budget
    (w : FixedConfigurationWitness s c BD) (hc : 0 < c) (j : ℕ) (hj : j < k)
    (hE : ∀ i,0 < primeShellMass (scheduledPrimeShells k
      (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j i))
    (hL hR : CopiedConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q)
    (hmass : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j) hE).mass hR ≠ 0)
    (z z' : SupportedHistory (ranges (sourceFrequencyRate BD k) (wordSize k L:ℝ) j) j [])
    (hbudget : 2*(⌊Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        sourceAtomWidth k c)⌋₊:ℝ)*(bound (sourceFrequencyRate BD k) (wordSize k L:ℝ) j:ℝ) <
      Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1)-sourceCopiedWidth k c)) :
    canonicalPairBounds k j (sourceWidth w.configuration (wordSize k L))
      (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
      (sourceRecurrenceV BD k L) (sourcePivotRanges w.configuration s.J (gapSchedule BD k L) c)
      (sourceRangeLeafMask k s.J (s.locations.X:ℝ) (initialGap BD k L) (configurationProductWidth k c))
      (s.locations.X:ℝ) (initialGap BD k L) (configurationProductWidth k c)
      hL hR y z.val.1 z'.val.1 z.val.2 z'.val.2 := by
  intro P hP _ hret
  refine ⟨sourceRecurrenceB_pivot_le _ _ _ _ _ _ hP,
    sourceRecurrenceV_root_bound BD k L j _ z,
    sourceRecurrenceV_root_bound BD k L j _ z',?_⟩
  have hh := (fixedConfiguration_copied_window w hc j hj hE hR hmass
    (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
    (sourceRecurrenceV BD k L)
    (canonicalHistoryExtra k (sourcePivotRanges w.configuration s.J (gapSchedule BD k L) c))
    (P:ℤ) z'.val.1 (outsideSampleState (schedule k j) j
      (sourceWidth w.configuration (wordSize k L)) y) z'.val.2 hret).1
  have hlt := hbudget.trans_le hh
  rw [prod_copiedSampleState]
  unfold sourceRecurrenceB sourceRecurrenceV
  exact_mod_cast hlt

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
