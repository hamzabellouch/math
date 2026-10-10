import OAI.Analysis.CircleDomains.Probability.ParametricNullTuples

namespace OAI

/-! Independent active tag tuples avoid every product-null tuple event.
Inactive slots carry no tuple mass. -/

open Set Filter Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def activeSlotPairs (E : Set (LevelTuple × LevelTuple)) : Set (TagSlot × TagSlot) :=
  {p | ∃ q r, p.1 = Sum.inr q ∧ p.2 = Sum.inr r ∧ (tagDataTuple q, tagDataTuple r) ∈ E}

theorem measurableSet_activeSlotPairs (E : Set (LevelTuple × LevelTuple))
    (hE : MeasurableSet E) : MeasurableSet (activeSlotPairs E) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have hi : Topology.IsOpenEmbedding activeTagSlot := Topology.IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  have he : activeSlotPairs E = Prod.map activeTagSlot activeTagSlot ''
      (Prod.map tagDataTuple tagDataTuple ⁻¹' E) := by
    ext p
    constructor
    · rintro ⟨q, r, hq, hr, hqr⟩
      exact ⟨(q, r), hqr, Prod.ext hq.symm hr.symm⟩
    · rintro ⟨⟨q, r⟩, hqr, rfl⟩
      exact ⟨q, r, rfl, rfl, hqr⟩
  rw [he]
  apply (hme.prodMap hme).measurableSet_image.mpr
  exact hE.preimage (continuous_tagDataTuple.measurable.prodMap continuous_tagDataTuple.measurable)

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_active_slots_avoid (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k q,
      Γ.val.2 k = Sum.inr q → tagDataTuple q ∉ A := by
  filter_upwards [ae_slots_zero_on_null_tuples d P τ hτ A hA hz] with Γ hΓ
  intro k q hq hmem
  have h := hΓ k
  rw [hq, slotTupleMeasure, Sum.elim_inr, Measure.dirac_apply' _ hA,
    indicator_of_mem hmem, Pi.one_apply] at h
  exact one_ne_zero h

theorem ae_slot_pair_avoids_product_null
    (d e : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (τ : Measure LevelTuple) [SFinite τ]
    (hP : meanCodeTuple d P ≪ τ) (hQ : meanCodeTuple e Q ≪ τ)
    (E : Set (LevelTuple × LevelTuple)) (hzero : (τ.prod τ) E = 0) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ k l q r, p.1.val.2 k = Sum.inr q → p.2.val.2 l = Sum.inr r →
        (tagDataTuple q, tagDataTuple r) ∉ E := by
  obtain ⟨E', hEE', hE', hz⟩ := exists_measurable_superset_of_null hzero
  let A : Set LevelTuple := {t | τ (Prod.mk t ⁻¹' E') ≠ 0}
  have hA : MeasurableSet A := ((measurable_measure_prodMk_left hE')
    (measurableSet_singleton 0)).compl
  have hzA : τ A = 0 := by
    have h := Measure.measure_ae_null_of_prod_null hz
    change ∀ᵐ t ∂τ, τ (Prod.mk t ⁻¹' E') = 0 at h
    exact ae_iff.mp h
  have hfirst := ae_active_slots_avoid d P τ hP A hA hzA
  have hpair (k l : ℕ) :
      ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
        (p.1.val.2 k, p.2.val.2 l) ∉ activeSlotPairs E' := by
    have hmeas : MeasurableSet {p : BasePathCode d × BasePathCode e |
        (p.1.val.2 k, p.2.val.2 l) ∉ activeSlotPairs E'} :=
      (measurableSet_activeSlotPairs E' hE').compl.preimage
        (((measurable_pi_apply k).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_fst))).prodMk
        ((measurable_pi_apply l).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_snd))))
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [hfirst] with Γ hΓ
    cases hslot : Γ.val.2 k with
    | inl a =>
      apply Eventually.of_forall
      intro Δ h
      obtain ⟨q, r, hq, _, _⟩ := h
      change (Sum.inl a : TagSlot) = Sum.inr q at hq
      cases hq
    | inr q =>
      have hsec : τ (Prod.mk (tagDataTuple q) ⁻¹' E') = 0 := by
        exact not_ne_iff.mp (hΓ k q hslot)
      filter_upwards [ae_active_slots_avoid e Q τ hQ _
        (hE'.preimage (measurable_const.prodMk measurable_id)) hsec] with Δ hΔ
      rintro ⟨q', r, hq', hr, hqr⟩
      have hqq' : q = q' := Sum.inr.inj hq'
      subst q'
      exact hΔ l r hr hqr
  have hall := ae_all_iff.mpr fun k => ae_all_iff.mpr (hpair k)
  filter_upwards [hall] with p hp
  intro k l q r hq hr hmem
  exact hp k l ⟨q, r, hq, hr, hEE' hmem⟩

end CircleDomainRigidity

end

end OAI
