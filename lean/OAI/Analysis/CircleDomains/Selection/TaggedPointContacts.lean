import OAI.Analysis.CircleDomains.Probability.SlotLawMeasures
import OAI.Analysis.CircleDomains.Modulus.TupleIncidence

namespace OAI

/-! For a free point, absolute continuity of tuple laws removes every open
tag contact. A hit at that point must then be a residual contact. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] in
theorem no_tag_contact_of_slot_zero (H : ℕ → Set (UnitAddCircle × X))
    (hH : ∀ i, IsClosed (H i)) (Γ : TaggedPath X) (x : X) (k : ℕ)
    (hcontain : (Γ.1, Γ.2 k) ∈ tagContainment H)
    (hzero : slotTupleMeasure (Γ.2 k) (tupleIncident H x) = 0)
    (t : PathTime) (ht : Γ.1 t = x) :
    ¬ (tagLeft (Γ.2 k) < t ∧ t < tagRight (Γ.2 k)) := by
  rintro ⟨hl, hr⟩
  have hc := hcontain t hl hr
  rw [ht] at hc
  cases hs : Γ.2 k with
  | inl u =>
    simp only [hs, tagLeft, Sum.elim_inl] at hl
    exact (not_lt_of_ge le_top) hl
  | inr q =>
    have hmem : tagDataTuple q ∈ tupleIncident H x := by
      change ∃ j, (q.2.2.1 j, x) ∈ H (q.2.1 j)
      simpa only [hs, tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq] using hc
    rw [hs, slotTupleMeasure, Sum.elim_inr,
      Measure.dirac_apply' _ (isClosed_tupleIncident hH x).measurableSet,
      indicator_of_mem hmem, Pi.one_apply] at hzero
    exact one_ne_zero hzero

theorem path_hit_iff_residual_of_slot_zero (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (Γ : BasePathCode d) {x : X} (hx : x ∈ d.dust)
    (hz : ∀ k, slotTupleMeasure (Γ.val.2 k) (tupleIncident d.levels x) = 0) :
    x ∈ Set.range Γ.val.1 ↔ x ∈ residualImage d.dust Γ.val := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ⟨by simpa only [ht] using hx, fun k => ?_⟩, ht⟩
    by_cases hl : t ≤ tagLeft (Γ.val.2 k)
    · exact Or.inl hl
    · right
      by_contra hr
      exact no_tag_contact_of_slot_zero d.levels hH Γ.val x k
        (Γ.property.1.2.1 k).2.1 (hz k) t ht ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩

theorem ae_slot_incidence_zero (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (x : X) (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ∀ k, slotTupleMeasure (Γ.val.2 k) (tupleIncident d.levels x) = 0 := by
  apply ae_all_iff.mpr
  intro k
  have hA := (isClosed_tupleIncident hH x).measurableSet
  have hz := slotLaw_absolutelyContinuous d P (tupleReference ω) hτ k
    (tupleReference_incident_null hH ω x hx)
  rw [slotLaw_apply d P k hA] at hz
  exact (lintegral_eq_zero_iff ((Measure.measurable_coe hA).comp
    (measurable_baseCodeSlot d k))).mp hz

theorem ae_path_hit_iff_residual (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {x : X} (hx : x ∈ d.dust)
    (hfree : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      x ∈ Set.range Γ.val.1 ↔ x ∈ residualImage d.dust Γ.val :=
  (ae_slot_incidence_zero d hH P ω hτ x hfree).mono fun Γ hΓ =>
    path_hit_iff_residual_of_slot_zero d hH Γ hx hΓ

end CircleDomainRigidity

end

end OAI
