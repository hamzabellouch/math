import OAI.Analysis.CircleDomains.Selection.AffineResidualExposure
import OAI.Analysis.CircleDomains.Selection.NarrowedResidualBounds
import OAI.Analysis.CircleDomains.Modulus.TimeIncidenceReparametrization
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Affine restriction preserves the full family of residual incidence
inequalities. Rational tests in the old parameter suffice, despite the
generally irrational endpoints of the retained interval. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

theorem residualIncidenceBound_affine_open (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (ν : Measure Z) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) (c d : PathTime)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hbound : ResidualIncidenceBound B
      (Ioo (affinePathTime a b c) (affinePathTime a b d)) R P ν m Γ) :
    ResidualIncidenceBound B (Ioo c d) R P ν m (affineRestrictedTaggedPath a b Γ) := by
  have hi : Ioo c d ⊆ Ioo (⊥ : PathTime) ⊤ := fun _ ht =>
    ⟨lt_of_le_of_lt bot_le ht.1, lt_of_lt_of_le ht.2 le_top⟩
  have he := (affinePathTime a b).continuous.image_Ioo_of_strictMono
    (affinePathTime_strictMono hab) (a := c) (b := d)
  unfold ResidualIncidenceBound at hbound ⊢
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll] at hbound ⊢
  rw [← he, timeIncidence_restrict, timeToll_restrict _ _ (affinePathTime_strictMono hab).injective]
    at hbound
  apply timeIncidence_bound_of_countable_difference R P (affineRestrictedPath a b Γ.1)
    ((affinePathTime a b ⁻¹' residualTimes B Γ) ∩ Ioo c d)
    (residualTimes B (affineRestrictedTaggedPath a b Γ) ∩ Ioo c d) ν m hpoint _ _ hbound
  · exact inter_subset_inter_left _ (affine_old_residual_subset B hab Γ)
  · apply (affine_exposed_image_countable B hab Γ).mono
    rintro x ⟨t, ⟨ht, hnot⟩, rfl⟩
    exact ⟨t, ⟨⟨ht.1, hi ht.2⟩, fun hold => hnot ⟨hold, ht.2⟩⟩, rfl⟩

theorem residualConstraintFamily_affine (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (hΓ : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x)
    {a b : PathTime} (hab : a < b) :
    ResidualConstraintFamily B R P ν m (affineRestrictedTaggedPath a b Γ) := by
  intro i n c d
  apply residualIncidenceBound_closed_of_open B (R i) (P i n) (ν i) (m i)
    (affineRestrictedTaggedPath a b Γ) (hpoint i) _ c.toTime d.toTime
  intro s t
  exact residualIncidenceBound_affine_open B (R i) (P i n) Γ (ν i) (m i) hab s t
    (hpoint i) (residualConstraintFamily_open B R P ν m Γ hΓ i n _ _)

end CircleDomainRigidity

end

end OAI
