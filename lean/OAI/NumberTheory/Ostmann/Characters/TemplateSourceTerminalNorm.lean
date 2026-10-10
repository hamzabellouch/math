import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceEnergy
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter DiagonalEstimate
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (B V : (l:ℕ) → State k (l+1) → ℤ) (j : ℕ)

abbrev sourceRootFunction :=
  unitTerminalRootIntegrand k j (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j)

def sourceRootEnergy : ℝ :=
  (constituentPrimePrior (schedule k j) (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).mean (fun x =>
      ∑v : ↥(ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j []),
        ‖sourceRootFunction w B V j x v‖^2)

end

theorem eventually_sourceRootEnergy_le (d : Decomposition) (k j : ℕ) (hj : j≤k)
    {δ α β ρ γ c₀ c BD : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hBD : 0<BD) :
    ∀ᶠ L : ℝ in atTop,∀ E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀B V : (l:ℕ) → State k (l+1) → ℤ,
      sourceRootEnergy w B V j ≤ Real.exp ((β+1)*(2:ℝ)^j*L+(wordSize k L:ℝ)) := by
  have hb : 0<BD+20*Real.log (depthScale k) := by
    rw [depthScale,Real.log_exp]
    positivity
  have hnumα : ∀ᶠ L : ℝ in atTop,1≤α*L :=
    (Filter.tendsto_id.const_mul_atTop hα).eventually_ge_atTop 1
  have hnumρ : ∀ᶠ L : ℝ in atTop,1≤ρ*L :=
    (Filter.tendsto_id.const_mul_atTop hρ).eventually_ge_atTop 1
  filter_upwards [unitTerminalRoot_norm_eventually j k hj (z:=depthScale k)
      (a:=BD+20*Real.log (depthScale k)) (α:=α) (β:=β) (c:=0) (δ:=1)
      (depthScale_pos k) hb hα (hα.trans hαβ).le (by norm_num) (by norm_num)
      (configurationProductWidth k c),
    eventually_higherSource_collisionScale10 k α hα,hnumα,hnumρ,
    eventually_gt_atTop (0:ℝ),(wordSize_tendsto k).eventually_ge_atTop 1]
    with L hnorm hcut hαL hρL hL hm
  intro E hE hband s w B V
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
  have he := hnorm s.locations.Q (s.locations.base 0) s.bulk_pos
    (by simpa only [zero_mul,neg_zero,Real.exp_zero] using hρL.trans hmass)
    (fun p hp=>(hbulkLog p hp).1) (fun p hp=>(hbulkLog p hp).2)
    k (sourceWidth w.configuration (wordSize k L)) hw
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (fixedConfiguration_chosenPrime_shell w (by exact_mod_cast hm) hw j)
    (fun i p hp=>(fixedConfiguration_scheduled_log_bounds w hband j i p hp).1)
    (sourceScheduledUnits w j) (fixedConfiguration_scheduled_unit_norm w j)
    (sourceScheduledCharacters w j) (fixedConfiguration_scheduled_nonprincipal w j)
    (sourceScheduledCenters w j) B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (fixedConfiguration_X_pos w)
  simpa +instances only [sourceRootEnergy,sourceRootFunction,initialGap,wordSize,add_zero,one_mul] using he

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
