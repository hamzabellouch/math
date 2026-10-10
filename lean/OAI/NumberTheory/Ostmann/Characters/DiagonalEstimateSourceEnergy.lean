import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
open HigherBiasSourceWord Filter
attribute [local instance] Classical.propDecidable

theorem eventually_sourceMatchingAverage_le (d : Decomposition) (k j : ℕ) (hj : j<k)
    {δ α β ρ γ c₀ c BD : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc : 0<c) (hBD : 0<BD) :
    ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀B V : (l:ℕ) → State k (l+1) → ℤ,
      ∀A : Finset (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)),
      sourceMatchingAverage w j hj B V A ≤
        ((A.card:ℝ)*copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
          (s.locations.base 0) (s.locations.base 2) s.locations.primes))*
        Real.exp (-gapSchedule BD k L (j+1)+(sourceCopiedWidth k c+sourceAtomWidth k c))*
        Real.exp ((β+1)*(2:ℝ)^j*L+(wordSize k L:ℝ)) := by
  have hb : 0<BD+20*Real.log (depthScale k) := by
    rw [depthScale,Real.log_exp]
    positivity
  have hnumα : ∀ᶠ L : ℝ in atTop,1≤α*L :=
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  have hnumρ : ∀ᶠ L : ℝ in atTop,1≤ρ*L :=
    (Filter.tendsto_id.const_mul_atTop hρ).eventually_ge_atTop 1
  filter_upwards [eventually_unitMatchingAverage_le j k hj.le (z:=depthScale k)
      (b:=BD+20*Real.log (depthScale k)) (α:=α) (β:=β) (c:=0) (δ:=1)
      (depthScale_pos k) hb hα (hα.trans hαβ).le (by norm_num) (by norm_num)
      (configurationProductWidth k c),
    exists_actual_frequency_cutoff_eventually k hBD.le hα,
    eventually_higherSource_collisionScale10 k α hα,hnumα,hnumρ,
    eventually_gt_atTop (0:ℝ),(wordSize_tendsto k).eventually_ge_atTop 1]
    with L hnorm hfreq hcut hαL hρL hL hm
  intro E hE hband s w B V A
  obtain ⟨U,hS,hU⟩ := hfreq
  have hu : 0 ≤ s.locations.u := by linarith [s.locations.top_lower]
  have hmass := (source_base_mass s.locations hu (mul_nonneg hγ.le hL.le)
    hE (hcut s.locations.u s.locations.top_lower)).1
  have hbulkLog : ∀p∈s.locations.base 0,
      Real.exp (α*L)≤Real.log p.val ∧ Real.log p.val≤Real.exp (β*L) := by
    intro p hp
    have hglobal : p∈s.locations.primes := boundedInterval_subset _ _ _ hp
    have h := hband p.val (mem_boundedPrimeSet.mp hglobal)
    have hpos : 0<Real.log p.val := Real.log_pos (by exact_mod_cast (primeUpTo_prime p).one_lt)
    have hl := Real.exp_le_exp.mpr h.1
    have hu' := Real.exp_le_exp.mpr h.2
    rw [Real.exp_log hpos] at hl hu'
    exact ⟨hl,hu'⟩
  have hw : 0<sourceWidth w.configuration (wordSize k L) .word := by
    rw [sourceWidth_word]
    omega
  have hbound := hnorm s.locations.Q U (s.locations.base 0) s.bulk_pos
    (by simpa only [zero_mul,neg_zero,Real.exp_zero] using hρL.trans hmass)
    (fun p hp=>(hbulkLog p hp).1) (fun p hp=>(hbulkLog p hp).2)
    k hj (sourceWidth w.configuration (wordSize k L)) hw
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (fixedConfiguration_chosenPrime_shell w (by exact_mod_cast hm) hw j)
    (sourceScheduledUnits w j) (fixedConfiguration_scheduled_unit_norm w j)
    (sourceScheduledCharacters w j) (fixedConfiguration_scheduled_nonprincipal w j)
    (sourceScheduledCenters w j) B V (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (fixedConfiguration_X_pos w)
    (fun i p hp=>hU p.val (fixedConfiguration_scheduled_log_bounds w hband j i p hp).1)
    (hS j hj.le) (sourcePivotRanges w j) A
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j)
    (gapSchedule BD k L (j+1)) (sourceCopiedWidth k c) (sourceAtomWidth k c)
    (fun P hP=>pivotWindow_upper _ _ hP) (by
      intro P hP y hy f hf q hq
      have hret := (mul_ne_zero_iff.mp hq).1
      exact (fixedConfiguration_copied_window w hc j hj (sourceScheduledShells_pos w j)
        f hf B V (canonicalHistoryExtra k (sourcePivotRanges w)) (P:ℤ) q.val.1
        (outsideSampleState (schedule k j) j (sourceWidth w.configuration (wordSize k L)) y)
        q.val.2 hret).1)
  have hsource : actualCopiedShells w.configuration (wordSize k L) j
      (s.locations.base 0) (s.locations.base 2) s.locations.primes =
      fun i=>sourceScheduledShells w j
        (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i) := rfl
  rw [hsource]
  simpa only [sourceMatchingAverage,initialGap,wordSize,add_zero,one_mul,add_assoc] using hbound

end Ostmann.Characters.DiagonalEstimate

end

end OAI
