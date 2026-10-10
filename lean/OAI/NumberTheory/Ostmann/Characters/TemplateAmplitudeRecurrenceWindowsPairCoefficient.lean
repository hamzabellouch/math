import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceFrequencySum
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.RetainedRow
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem pairCoefficient_ne_zero_weights {α γ : Type*} [Fintype α] [Fintype γ]
    (k j : ℕ) (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (h : α → CopiedState k j) (y : γ → OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (phase : γ → ℕ+ → α → SupportedHistory S j path → ℂ)
    (a : γ) (x x' : α) (z z' : SupportedHistory S j path) (P : ℕ+)
    (hc : pairCoefficient k j B V extra mask X Δ W h y S path phase a x x' z z' P ≠ 0) :
    retainedHistoryWeight k B V extra mask X Δ W j z.val.1
      (sourceState k j (P:ℤ) (h x) (y a)) z.val.2 ≠ 0 ∧
    retainedHistoryWeight k B V extra mask X Δ W j z'.val.1
      (sourceState k j (P:ℤ) (h x') (y a)) z'.val.2 ≠ 0 := by
  constructor
  · intro hn
    exact hc (by simp only [pairCoefficient,term,hn,zero_mul])
  · intro hn
    exact hc (by simp only [pairCoefficient,term,hn,zero_mul,map_zero,mul_zero])

end Ostmann.Characters.Template.RetainedRow

namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds InitialCharacterScale HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem fixedConfiguration_pairCoefficient_copied_bound
    {d : Decomposition} {E₀ : Finset ℕ} {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E₀ δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hc : 0 < c) (j : ℕ) (hj : j < k)
    (hE : ∀ i,0 < primeShellMass (scheduledPrimeShells k
      (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j i))
    (hL hR : CopiedConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q)
    (hmL : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j) hE).mass hL ≠ 0)
    (hmR : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j) hE).mass hR ≠ 0)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (phase : (OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
        PrimeUpTo s.locations.Q) → ℕ+ →
      (CopiedConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
        PrimeUpTo s.locations.Q) → SupportedHistory S j path → ℂ)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q)
    (z z' : SupportedHistory S j path) (P : ℕ+)
    (hcoef : RetainedRow.pairCoefficient k j B V
      (canonicalHistoryExtra k (sourcePivotRanges w.configuration s.J (gapSchedule BD k L) c))
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J (s.locations.X:ℝ)
        (initialGap BD k L) (configurationProductWidth k c)))
      (s.locations.X:ℝ) (initialGap BD k L) (configurationProductWidth k c)
      (copiedSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)))
      (outsideSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)))
      S path phase y hL hR z z' P ≠ 0) :
    |((∏ i,copiedSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)) hL i:ℤ):ℝ)| ≤
      Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1)+sourceCopiedWidth k c) ∧
    |((∏ i,copiedSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)) hR i:ℤ):ℝ)| ≤
      Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1)+sourceCopiedWidth k c) := by
  obtain ⟨hl,hr⟩ := RetainedRow.pairCoefficient_ne_zero_weights k j B V _ _ _ _ _ _ _
    S path phase y hL hR z z' P hcoef
  have hleft := (fixedConfiguration_copied_window w hc j hj hE hL hmL B V _
    (P:ℤ) z.val.1 (outsideSampleState (schedule k j) j
      (sourceWidth w.configuration (wordSize k L)) y) z.val.2 hl).2
  have hright := (fixedConfiguration_copied_window w hc j hj hE hR hmR B V _
    (P:ℤ) z'.val.1 (outsideSampleState (schedule k j) j
      (sourceWidth w.configuration (wordSize k L)) y) z'.val.2 hr).2
  rw [prod_copiedSampleState,prod_copiedSampleState]
  simp only [Int.cast_natCast]
  constructor
  · rw [abs_of_nonneg (show (0:ℝ) ≤ ((∏ i,(hL i).val:ℕ):ℝ) from Nat.cast_nonneg _)]
    exact hleft
  · rw [abs_of_nonneg (show (0:ℝ) ≤ ((∏ i,(hR i).val:ℕ):ℝ) from Nat.cast_nonneg _)]
    exact hright

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
