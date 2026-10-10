import OAI.Analysis.CircleDomains.Topology.RationalTimeIntervals

namespace OAI

/-! The coded residual-contact inequalities extend from rational closed
intervals to every open time interval, by directed continuity from below. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem residualIncidence_time_mono (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) {I J : Set PathTime} (hIJ : I ⊆ J) :
    {z | (Γ, z) ∈ residualIncidence B I R P} ⊆
      {z | (Γ, z) ∈ residualIncidence B J R P} := by
  rintro z ⟨t, ht, hI, hR, hP⟩
  exact ⟨t, ht, hIJ hI, hR, hP⟩

omit [MeasurableSpace Z] in
theorem residualToll_time_mono (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    {I J : Set PathTime} (hIJ : I ⊆ J) : residualToll B I m Γ ≤ residualToll B J m Γ := by
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ I
  · have htJ : t ∈ residualTimes B Γ ∧ t ∈ J := ⟨ht.1, hIJ ht.2⟩
    simp only [ite_eq_left ht, ite_eq_left htJ]
    exact le_rfl
  · simp only [ite_eq_right ht]
    exact bot_le

omit [MeasurableSpace Z] in
theorem residualIncidence_time_iUnion {ι : Type*} (B : Set X) (R : Set (Z × X))
    (P : Set X) (Γ : TaggedPath X) (I : ι → Set PathTime) :
    {z | (Γ, z) ∈ residualIncidence B (⋃ i, I i) R P} =
      ⋃ i, {z | (Γ, z) ∈ residualIncidence B (I i) R P} := by
  ext z
  constructor
  · rintro ⟨t, ht, hI, hR, hP⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hI
    exact mem_iUnion.mpr ⟨i, t, ht, hi, hR, hP⟩
  · intro h
    obtain ⟨i, t, ht, hi, hR, hP⟩ := mem_iUnion.mp h
    exact ⟨t, ht, mem_iUnion.mpr ⟨i, hi⟩, hR, hP⟩

theorem residualIncidenceBound_directed_union {ι : Type*} [Countable ι]
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X) (I : ι → Set PathTime) (hd : Directed (· ⊆ ·) I)
    (h : ∀ i, ResidualIncidenceBound B (I i) R P ν m Γ) :
    ResidualIncidenceBound B (⋃ i, I i) R P ν m Γ := by
  have hdir : Directed (· ⊆ ·) (fun i => {z | (Γ, z) ∈ residualIncidence B (I i) R P}) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, residualIncidence_time_mono B R P Γ hik, residualIncidence_time_mono B R P Γ hjk⟩
  unfold ResidualIncidenceBound
  rw [residualIncidence_time_iUnion, hdir.measure_iUnion]
  exact iSup_le fun i => (h i).trans
    (residualToll_time_mono B (deletedWeight P m) Γ (subset_iUnion I i))

theorem residualIncidenceBound_open_of_rational
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (h : ∀ a b : RationalPathTime, ResidualIncidenceBound B (Icc a.toTime b.toTime) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Ioo a b) R P ν m Γ := by
  rw [← iUnion_innerRationalInterval a b]
  exact residualIncidenceBound_directed_union B R P ν m Γ (innerRationalInterval a b)
    (innerRationalInterval_directed a b) (fun p => h p.val.1 p.val.2)

theorem residualConstraintFamily_open (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (h : ResidualConstraintFamily B R P ν m Γ)
    (i n : ℕ) (a b : PathTime) :
    ResidualIncidenceBound B (Ioo a b) (R i) (P i n) (ν i) (m i) Γ :=
  residualIncidenceBound_open_of_rational B (R i) (P i n) (ν i) (m i) Γ (h i n) a b

end CircleDomainRigidity

end

end OAI
