import OAI.Analysis.CircleDomains.Selection.NarrowedTags

namespace OAI

/-! The countable image exposed by discarding constant tag pieces is paid
by singleton bounds. This preserves all incidence constraints on the retained
open interval, even if the new residual set has uncountably many times. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*} [MeasurableSpace Z]

theorem timeIncidence_bound_of_countable_difference
    (R : Set (Z × X)) (P : Set X) (γ : T → X) (A C : Set T)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hAC : A ⊆ C)
    (hcount : (γ '' (C \ A)).Countable)
    (hbound : ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤
      timeToll γ A (deletedWeight P m)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ C) ≤
      timeToll γ C (deletedWeight P m) := by
  have he : (C \ A) ∪ A = C := sdiff_union_of_subset hAC
  rw [← he, timeIncidence_union, timeToll_union γ _ disjoint_sdiff_left]
  exact (measure_union_le _ _).trans (add_le_add
    (countable_image_deleted_incidence_bound R P γ (C \ A) ν m hpoint hcount) hbound)

variable [MetricSpace X]

theorem residualIncidenceBound_narrow (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (ν : Measure Z) (m : X → ℝ≥0∞) (a b : PathTime)
    (I : Set PathTime) (hI : I ⊆ Ioo a b)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hbound : ResidualIncidenceBound B I R P ν m Γ) :
    ResidualIncidenceBound B I R P ν m (narrowTaggedPath a b Γ) := by
  unfold ResidualIncidenceBound at *
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll] at hbound ⊢
  apply timeIncidence_bound_of_countable_difference R P Γ.1
    (residualTimes B Γ ∩ I) (residualTimes B (narrowTaggedPath a b Γ) ∩ I)
    ν m hpoint _ _ hbound
  · exact inter_subset_inter_left I (residualTimes_subset_narrow B a b Γ)
  · apply (newly_exposed_narrow_image_countable B a b Γ).mono
    rintro x ⟨t, ⟨ht, hnot⟩, rfl⟩
    exact ⟨t, ⟨⟨ht.1, hI ht.2⟩, fun hold => hnot ⟨hold, ht.2⟩⟩, rfl⟩

omit [MeasurableSpace Z] in
theorem residualImage_narrow_null [MeasurableSpace X] (B : Set X) (Γ : TaggedPath X)
    (a b : PathTime) (ν : Measure X) [MeasurableSingletonClass X] [NullSingletonClass ν]
    (hnull : ν (residualImage B Γ) = 0) :
    ν (Γ.1 '' (residualTimes B (narrowTaggedPath a b Γ) ∩ Ioo a b)) = 0 := by
  have hsub : Γ.1 '' (residualTimes B (narrowTaggedPath a b Γ) ∩ Ioo a b) ⊆
      residualImage B Γ ∪
        Γ.1 '' ((residualTimes B (narrowTaggedPath a b Γ) ∩ Ioo a b) \ residualTimes B Γ) := by
    rintro x ⟨t, ht, rfl⟩
    by_cases hold : t ∈ residualTimes B Γ
    · exact Or.inl ⟨t, hold, rfl⟩
    · exact Or.inr ⟨t, ⟨ht, hold⟩, rfl⟩
  apply le_antisymm _ bot_le
  exact (measure_mono hsub).trans (by
    rw [measure_union_null hnull ((newly_exposed_narrow_image_countable B a b Γ).measure_zero ν)]
    exact le_rfl)

end CircleDomainRigidity

end

end OAI
