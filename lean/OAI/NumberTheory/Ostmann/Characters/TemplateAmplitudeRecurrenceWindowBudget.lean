import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowBudgetPair
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowBudgetScalar
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsPairCoefficient
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceAmplitude

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds InitialCharacterScale
open HistoryFrequencyBudget HistoryFrequencyLabels DiagonalEstimate Filter
attribute [local instance] Classical.propDecidable

lemma terminalFrequencyCutoff_mono {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    {j k : ℕ} (hj : j ≤ k) : terminalFrequencyCutoff a m j ≤ terminalFrequencyCutoff a m k := by
  have h₂ : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj
  have h₄ : (4:ℝ)^j ≤ 4^k := pow_le_pow_right₀ (by norm_num) hj
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ hm
  unfold linearEnvelope
  gcongr

theorem eventually_fixedConfiguration_sourceTransferBounds (k : ℕ) (BD c α : ℝ)
    (hBD : 1 ≤ BD) (hc : 0<c) (hα : 0<α) :
    ∀ᶠ L : ℝ in atTop, ∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ : ℝ),
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
      ∀j (hj : j<k), Nonempty (SourceTransferBounds w
        (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
        (sourceRecurrenceV BD k L) j hj) := by
  filter_upwards [eventually_source_recurrence_window_budget BD c k hBD,
    actualFrequencyCutoff_eventually k (zero_le_one.trans hBD) hα] with L hnum hfreq
  intro d E δ β ρ γ c₀ hband s w j hj
  have hrate := sourceFrequencyRate_nonneg hBD k
  have hnumj := hnum j (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j)
  refine ⟨{
    prime_gt := ?_
    hBounds := ?_
    Hmax := Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
      gapSchedule BD k L (j+1)+sourceCopiedWidth k c)
    Pmin := Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j-sourceAtomWidth k c)
    hcopied := ?_
    hPmin := Real.exp_pos _
    hpivot := ?_
    hcap := ?_
    hR := ?_ }⟩
  · intro i p hp
    have hu := hfreq.2 p.val (fixedConfiguration_scheduled_log_bounds w hband 0 i p hp).1
    exact (terminalFrequencyCutoff_mono hrate (Nat.cast_nonneg (wordSize k L)) hj).trans_lt hu
  · intro y _ hL hR _ hmR z z'
    exact fixedConfiguration_canonicalPairBounds_of_budget w hc j hj (sourceScheduledShells_pos w j)
      hL hR y hmR z z' hnumj.1
  · intro y _ hL hR hmL hmR z z' P _ hcoef
    exact fixedConfiguration_pairCoefficient_copied_bound w hc j hj (sourceScheduledShells_pos w j)
      hL hR hmL hmR _ _ _ [] _ y z z' P hcoef
  · intro P hP
    exact sourcePivotRanges_lower w.configuration s.J (gapSchedule BD k L) c j hP
  · simpa only [Int.cast_natCast] using hnumj.2
  · intro q hq
    exact fixedConfiguration_pivot_mem w hc j hj q hq

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
