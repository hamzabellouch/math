import OAI.Analysis.CircleDomains.Selection.ReversedTags
import OAI.Analysis.CircleDomains.Modulus.TimeIncidenceReparametrization
import OAI.Analysis.CircleDomains.Topology.ResidualClosedIntervals

namespace OAI

/-! Reversal preserves the residual inequalities, with exactly reversed
test intervals and unchanged parameter multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem image_symm_Icc (a b : PathTime) :
    unitInterval.symm '' Icc a b = Icc (unitInterval.symm b) (unitInterval.symm a) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨unitInterval.symm_le_symm.mpr hs.2, unitInterval.symm_le_symm.mpr hs.1⟩
  · intro ht
    refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
    exact ⟨unitInterval.le_symm_comm.mpr ht.2, unitInterval.symm_le_comm.mpr ht.1⟩

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

theorem residualIncidenceBound_reversed (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X) (a b : PathTime)
    (h : ResidualIncidenceBound B (Icc (unitInterval.symm b) (unitInterval.symm a)) R P ν m Γ) :
    ResidualIncidenceBound B (Icc a b) R P ν m (reversedTaggedPath Γ) := by
  unfold ResidualIncidenceBound at h ⊢
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll] at h ⊢
  rw [← image_symm_Icc, timeIncidence_restrict,
    timeToll_restrict _ _ unitInterval.symm_bijective.injective] at h
  rw [residualTimes_reversed]
  exact h

theorem residualConstraintFamily_reversed (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (hΓ : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x) :
    ResidualConstraintFamily B R P ν m (reversedTaggedPath Γ) := by
  intro i n a b
  exact residualIncidenceBound_reversed B (R i) (P i n) (ν i) (m i) Γ a.toTime b.toTime
    (residualConstraintFamily_closed B R P ν m Γ hΓ hpoint i n _ _)

end CircleDomainRigidity

end

end OAI
