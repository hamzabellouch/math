import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsPivotRange
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsRetained

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds InitialCharacterScale
attribute [local instance] Classical.propDecidable

def sourcePivotRanges {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ) (gaps : ℕ → ℝ)
    (c : ℝ) (j : ℕ) : Finset ℕ+ :=
  pivotWindow (sourcePivotTarget cfg J gaps j) (sourceAtomWidth k c)

variable {d : Decomposition} {E₀ : Finset ℕ} {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
variable {s : SelectedWordSource d E₀ δ L k α β ρ γ c₀}

theorem fixedConfiguration_pivot_mem (w : FixedConfigurationWitness s c BD) (hc : 0 < c)
    (j : ℕ) (hj : j < k)
    (q : Fin (sourceWidth w.configuration (wordSize k L)
      ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo s.locations.Q)
    (hq : ∀ a,q a ∈ scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j
      ⟨(pivotSlot k j hj).val,a⟩) :
    PivotEliminationActual.positiveTupleProduct q ∈
      sourcePivotRanges w.configuration s.J (gapSchedule BD k L) c j := by
  rw [sourcePivotRanges,mem_pivotWindow_iff_abs_log]
  exact scheduled_pivot_atom_target w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes s.J (gapSchedule BD k L)
    (Real.log s.locations.X) c hc w.geometry.target_error w.geometry.length_upper
    (pivotSlot k j hj).val ⟨j,hj⟩ (pivotSlot k j hj).property.2 q hq

theorem fixedConfiguration_copied_window (w : FixedConfigurationWitness s c BD) (hc : 0 < c)
    (j : ℕ) (hj : j < k)
    (hE : ∀ i,0 < primeShellMass (scheduledPrimeShells k
      (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j i))
    (h : CopiedConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q)
    (hmass : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (scheduledPrimeShells k (sourceWidth w.configuration (wordSize k L))
      (configurationPrimeShells w.configuration (wordSize k L)
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) j) hE).mass h ≠ 0)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (P v : ℤ) (y : OutsideState k j) (t : HistoryReconstruction.Tree j)
    (hret : retainedHistoryWeight k B V extra
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J (s.locations.X:ℝ)
        (initialGap BD k L) (configurationProductWidth k c)))
      (s.locations.X:ℝ) (initialGap BD k L) (configurationProductWidth k c) j v
      (sourceState k j P (copiedSampleState (schedule k j) j
        (sourceWidth w.configuration (wordSize k L)) h) y) t ≠ 0) :
    Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
      gapSchedule BD k L (j+1)-sourceCopiedWidth k c) ≤ ((∏ i,(h i).val:ℕ):ℝ) ∧
    ((∏ i,(h i).val:ℕ):ℝ) ≤ Real.exp
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1)+sourceCopiedWidth k c) :=
  retained_source_copied_window w.configuration (wordSize k L) j
    (s.locations.base 0) (s.locations.base 2) s.locations.primes s.J (gapSchedule BD k L)
    (Real.log s.locations.X) c hj hc w.geometry.target_error w.geometry.length_upper hE h hmass
    B V extra (s.locations.X:ℝ) (initialGap BD k L) (configurationProductWidth k c) P v y t hret

theorem sourcePivotRanges_lower (cfg : SourceConfiguration k) (J : ℤ) (gaps : ℕ → ℝ)
    (c : ℝ) (j : ℕ) {P : ℕ+} (hP : P ∈ sourcePivotRanges cfg J gaps c j) :
    Real.exp (sourcePivotTarget cfg J gaps j-sourceAtomWidth k c) ≤ (P:ℝ) :=
  pivotWindow_lower _ _ hP

theorem sourcePivotRanges_upper (cfg : SourceConfiguration k) (J : ℤ) (gaps : ℕ → ℝ)
    (c : ℝ) (j : ℕ) {P : ℕ+} (hP : P ∈ sourcePivotRanges cfg J gaps c j) :
    (P:ℝ) ≤ Real.exp (sourcePivotTarget cfg J gaps j+sourceAtomWidth k c) :=
  pivotWindow_upper _ _ hP

theorem sourcePivotRanges_card_le (cfg : SourceConfiguration k) (J : ℤ) (gaps : ℕ → ℝ)
    (c : ℝ) (j : ℕ) : ((sourcePivotRanges cfg J gaps c j).card:ℝ) ≤
      Real.exp (sourcePivotTarget cfg J gaps j+sourceAtomWidth k c) :=
  pivotWindow_card_le _ _

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
