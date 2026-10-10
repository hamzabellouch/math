import OAI.Analysis.CircleDomains.Modulus.CountableImageIncidence

namespace OAI

/-! Assembly of residual-contact estimates on disjoint time pieces. No
disjointness of their images is required: a repeated visit is paid again. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

theorem timeIncidence_union (R : Set (Z × X)) (γ : T → X) (A C : Set T) :
    timeIncidence R γ (A ∪ C) = timeIncidence R γ A ∪ timeIncidence R γ C := by
  ext z
  constructor
  · rintro ⟨t, ht | ht, hr⟩
    · exact Or.inl ⟨t, ht, hr⟩
    · exact Or.inr ⟨t, ht, hr⟩
  · rintro (⟨t, ht, hr⟩ | ⟨t, ht, hr⟩)
    · exact ⟨t, Or.inl ht, hr⟩
    · exact ⟨t, Or.inr ht, hr⟩

theorem timeToll_union (γ : T → X) (m : X → ℝ≥0∞) {A C : Set T}
    (hdis : Disjoint A C) : timeToll γ (A ∪ C) m = timeToll γ A m + timeToll γ C m := by
  simp only [timeToll_eq_indicator]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro t
  by_cases ha : t ∈ A
  · have hc : t ∉ C := fun hc => disjoint_left.mp hdis ha hc
    simp [ha, hc]
  · simp [ha]

variable [MeasurableSpace Z]

theorem timeIncidence_bound_with_countable_remainder {ι : Type*} [Countable ι]
    (R : Set (Z × X)) (P : Set X) (γ : T → X) (A A₀ : Set T) (C : ι → Set T)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hcover : A = A₀ ∪ ⋃ i, C i)
    (hdis : Pairwise (Disjoint on C)) (hdis₀ : Disjoint A₀ (⋃ i, C i))
    (hcount : (γ '' A₀).Countable)
    (hbound : ∀ i, ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ (C i)) ≤
      timeToll γ (C i) (deletedWeight P m)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤
      timeToll γ A (deletedWeight P m) := by
  rw [hcover, timeIncidence_union, timeToll_union γ _ hdis₀,
    timeIncidence_iUnion, timeToll_iUnion γ _ C hdis]
  exact (measure_union_le _ _).trans (add_le_add
    (countable_image_deleted_incidence_bound R P γ A₀ ν m hpoint hcount)
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hbound)))

variable [MetricSpace X]

omit [MeasurableSpace Z] in
theorem residualIncidence_eq_timeIncidence (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (Γ : TaggedPath X) :
    {z | (Γ, z) ∈ residualIncidence B I R P} =
      timeIncidence {q | q ∈ R ∧ q.2 ∉ P} Γ.1 (residualTimes B Γ ∩ I) := by
  ext z
  constructor
  · rintro ⟨t, ht, hi, hr, hp⟩
    exact ⟨t, ⟨ht, hi⟩, hr, hp⟩
  · rintro ⟨t, ⟨ht, hi⟩, hr, hp⟩
    exact ⟨t, ht, hi, hr, hp⟩

omit [MeasurableSpace Z] in
theorem residualToll_eq_timeToll (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = timeToll Γ.1 (residualTimes B Γ ∩ I) m := by
  rw [timeToll_eq_indicator]
  unfold residualToll
  apply tsum_congr
  intro t
  by_cases h : t ∈ residualTimes B Γ ∧ t ∈ I <;> simp [h]

theorem residualIncidenceBound_of_countable_image (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (Γ : TaggedPath X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hcount : (Γ.1 '' (residualTimes B Γ ∩ I)).Countable) :
    ResidualIncidenceBound B I R P ν m Γ := by
  unfold ResidualIncidenceBound
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll]
  exact countable_image_deleted_incidence_bound R P Γ.1 _ ν m hpoint hcount

theorem residualIncidenceBound_of_disjoint_pieces {ι : Type*} [Countable ι]
    (B : Set X) (I : Set PathTime) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (A₀ : Set PathTime) (C : ι → Set PathTime)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hcover : residualTimes B Γ ∩ I = A₀ ∪ ⋃ i, C i)
    (hdis : Pairwise (Disjoint on C)) (hdis₀ : Disjoint A₀ (⋃ i, C i))
    (hcount : (Γ.1 '' A₀).Countable)
    (hbound : ∀ i, ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} Γ.1 (C i)) ≤
      timeToll Γ.1 (C i) (deletedWeight P m)) :
    ResidualIncidenceBound B I R P ν m Γ := by
  unfold ResidualIncidenceBound
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll]
  exact timeIncidence_bound_with_countable_remainder R P Γ.1 _ A₀ C ν m
    hpoint hcover hdis hdis₀ hcount hbound

end CircleDomainRigidity

end

end OAI
