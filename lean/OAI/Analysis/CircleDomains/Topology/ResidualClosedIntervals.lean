import OAI.Analysis.CircleDomains.Topology.ResidualOpenIntervals

namespace OAI

/-! Singleton incidence estimates supply the endpoints omitted by open
pieces. The original rational constraints therefore hold on every closed
time interval, without a local finiteness assumption on the prior toll. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem residualToll_union (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    {I J : Set PathTime} (hIJ : Disjoint I J) :
    residualToll B (I ∪ J) m Γ = residualToll B I m Γ + residualToll B J m Γ := by
  unfold residualToll
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro t
  by_cases hr : t ∈ residualTimes B Γ
  · by_cases hi : t ∈ I
    · have hj : t ∉ J := fun hj => Set.disjoint_left.mp hIJ hi hj
      simp [hr, hi, hj]
    · simp [hr, hi]
  · simp [hr]

omit [MeasurableSpace Z] in
theorem residualIncidence_time_union (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (I J : Set PathTime) :
    {z | (Γ, z) ∈ residualIncidence B (I ∪ J) R P} =
      {z | (Γ, z) ∈ residualIncidence B I R P} ∪
      {z | (Γ, z) ∈ residualIncidence B J R P} := by
  ext z
  constructor
  · rintro ⟨t, ht, hi | hj, hR, hp⟩
    · exact Or.inl ⟨t, ht, hi, hR, hp⟩
    · exact Or.inr ⟨t, ht, hj, hR, hp⟩
  · rintro (⟨t, ht, hi, hR, hp⟩ | ⟨t, ht, hj, hR, hp⟩)
    · exact ⟨t, ht, Or.inl hi, hR, hp⟩
    · exact ⟨t, ht, Or.inr hj, hR, hp⟩

theorem residualIncidenceBound_union (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X) {I J : Set PathTime}
    (hIJ : Disjoint I J) (hI : ResidualIncidenceBound B I R P ν m Γ)
    (hJ : ResidualIncidenceBound B J R P ν m Γ) :
    ResidualIncidenceBound B (I ∪ J) R P ν m Γ := by
  unfold ResidualIncidenceBound at *
  rw [residualIncidence_time_union, residualToll_union B (deletedWeight P m) Γ hIJ]
  exact (measure_union_le _ _).trans (add_le_add hI hJ)

omit [MeasurableSpace Z] in
theorem residualToll_singleton (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X) (a : PathTime) :
    residualToll B {a} m Γ = if a ∈ residualTimes B Γ then m (Γ.1 a) else 0 := by
  unfold residualToll
  rw [tsum_eq_single a (fun t ht => by simp [ht])]
  simp

theorem residualIncidenceBound_singleton (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (a : PathTime) :
    ResidualIncidenceBound B {a} R P ν m Γ := by
  by_cases h : a ∈ residualTimes B Γ ∧ Γ.1 a ∉ P
  · unfold ResidualIncidenceBound
    rw [residualToll_singleton, ite_eq_left h.1]
    have hsub : {z | (Γ, z) ∈ residualIncidence B {a} R P} ⊆ {z | (z, Γ.1 a) ∈ R} := by
      rintro z ⟨t, _, ht, hr, _⟩
      have he : t = a := ht
      change (z, Γ.1 a) ∈ R
      simpa only [he] using hr
    exact (measure_mono hsub).trans (by simpa [deletedWeight, h.2] using hpoint (Γ.1 a))
  · have hz : {z | (Γ, z) ∈ residualIncidence B {a} R P} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨t, ht, ha, _, hp⟩
      have he : t = a := ha
      exact h (he ▸ ⟨ht, hp⟩)
    unfold ResidualIncidenceBound
    rw [hz, measure_empty]
    exact bot_le

theorem residualIncidenceBound_closed_of_open
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (h : ∀ a b : PathTime, ResidualIncidenceBound B (Ioo a b) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Icc a b) R P ν m Γ := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hleft := residualIncidenceBound_singleton B R P ν m Γ hpoint a
    have hright := residualIncidenceBound_singleton B R P ν m Γ hpoint b
    have hopen := h a b
    have hdis : Disjoint ({a} : Set PathTime) (Ioo a b) := by simp
    have hfirst := residualIncidenceBound_union B R P ν m Γ hdis hleft hopen
    have hdis' : Disjoint (({a} : Set PathTime) ∪ Ioo a b) {b} := by simp [hab.ne']
    have hall := residualIncidenceBound_union B R P ν m Γ hdis' hfirst hright
    have he : (({a} : Set PathTime) ∪ Ioo a b) ∪ {b} = Icc a b := by
      rw [union_comm {a}, Ioo_union_left hab, Ico_union_right hab.le]
    rwa [he] at hall
  · simpa only [Icc_self] using residualIncidenceBound_singleton B R P ν m Γ hpoint a
  · simp [ResidualIncidenceBound, residualIncidence, residualToll, Icc_eq_empty_of_lt hba]

theorem residualIncidenceBound_closed_of_rational
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (h : ∀ a b : RationalPathTime, ResidualIncidenceBound B (Icc a.toTime b.toTime) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Icc a b) R P ν m Γ :=
  residualIncidenceBound_closed_of_open B R P ν m Γ hpoint
    (residualIncidenceBound_open_of_rational B R P ν m Γ h) a b

theorem residualConstraintFamily_closed (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (h : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x)
    (i n : ℕ) (a b : PathTime) :
    ResidualIncidenceBound B (Icc a b) (R i) (P i n) (ν i) (m i) Γ :=
  residualIncidenceBound_closed_of_rational B (R i) (P i n) (ν i) (m i) Γ
    (hpoint i) (h i n) a b

end CircleDomainRigidity

end

end OAI
