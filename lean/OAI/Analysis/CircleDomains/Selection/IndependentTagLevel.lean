import OAI.Analysis.CircleDomains.Selection.TagLevelSingleton
import OAI.Analysis.CircleDomains.Probability.SlotPairNull

namespace OAI

/-! Absolute continuity of tag tuples supplies the independent-level
singleton conclusion for almost every path and almost every level. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem tupleReference_product_right_null
    {T : Type*} [MeasurableSpace T] (ω : TupleType → ℝ≥0∞)
    (ν : Measure T) [SFinite ν] (E : Set (LevelTuple × T))
    (hE : ∀ i : TupleType,
      ((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod ν)
        (Prod.map (tupleFiber i) id ⁻¹' E) = 0) :
    ((tupleReference ω).prod ν) E = 0 := by
  rw [tupleReference, Measure.prod_sum_left, Measure.sum_apply_eq_zero]
  intro i
  rw [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  have hm := Measure.map_prod_map
    (volume : Measure (Fin (i.1 + 1) → UnitAddCircle)) ν
    (measurable_tupleFiber i) (measurable_id (α := T))
  rw [Measure.map_id] at hm
  rw [hm, ((measurableEmbedding_tupleFiber i).prodMap MeasurableEmbedding.id).map_apply,
    hE, mul_zero]

theorem tupleReference_single_level_incompatible_null
    {X : Type*} [TopologicalSpace X]
    (H : ℕ → Set (UnitAddCircle × X)) (Free : Set X)
    (hP : OrderedLevelNullCompatibility H Free)
    (ω : TupleType → ℝ≥0∞) (i : ℕ) :
    ((tupleReference ω).prod (volume : Measure UnitAddCircle))
      {p | ¬ TuplePairCompatible H Free p.1 (singleLevelTuple i p.2)} = 0 := by
  apply tupleReference_product_right_null
  intro q
  let r : TupleType := ⟨0, fun _ => i⟩
  have hleft := ae_finite_tuple_ordered_compatibility H Free hP q.2 r.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_finite_tuple_ordered_compatibility H Free hP r.2 q.2)
  have hg : ∀ᵐ p ∂((volume : Measure (Fin (q.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin 1 → UnitAddCircle))),
      TuplePairCompatible H Free (tupleFiber q p.1) (tupleFiber r p.2) := by
    filter_upwards [ae_torus_pair_distinct, hleft, hright] with p hp hl hr
    exact ⟨fun a b _ => hp a b, hl, hr⟩
  have he : MeasurePreserving
      (Prod.map (id : (Fin (q.1 + 1) → UnitAddCircle) → _)
        (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm)
      (volume.prod (volume : Measure UnitAddCircle)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (MeasureTheory.volume_preserving_funUnique (Fin 1) UnitAddCircle).symm
  have hh := he.quasiMeasurePreserving.ae hg
  exact ae_iff.mp hh

private def activeSlotParameterEvent {T : Type*} (E : Set (LevelTuple × T)) :
    Set (TagSlot × T) :=
  {p | ∃ q, p.1 = Sum.inr q ∧ (tagDataTuple q, p.2) ∈ E}

private theorem measurableSet_activeSlotParameterEvent
    {T : Type*} [MeasurableSpace T] (E : Set (LevelTuple × T)) (hE : MeasurableSet E) :
    MeasurableSet (activeSlotParameterEvent E) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot)
      Topology.IsOpenEmbedding.inr
  have he : activeSlotParameterEvent E =
      Prod.map activeTagSlot id '' (Prod.map tagDataTuple id ⁻¹' E) := by
    ext p
    constructor
    · rintro ⟨q, hq, hmem⟩
      exact ⟨(q, p.2), hmem, Prod.ext hq.symm rfl⟩
    · rintro ⟨⟨q, t⟩, hmem, rfl⟩
      exact ⟨q, rfl, hmem⟩
  rw [he]
  exact (hme.prodMap MeasurableEmbedding.id).measurableSet_image.mpr
    (hE.preimage (continuous_tagDataTuple.measurable.prodMap measurable_id))

theorem ae_active_slots_avoid_independent_null
    {X Y T : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X]
    [MeasurableSpace C(PathTime, X)] [MeasurableSpace T]
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (τ : Measure LevelTuple) [SFinite τ] (ν : Measure T) [SFinite ν]
    (hτ : meanCodeTuple d P ≪ τ) (E : Set (LevelTuple × T))
    (hzero : (τ.prod ν) E = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ t ∂ν,
      ∀ k q, Γ.val.2 k = Sum.inr q → (tagDataTuple q, t) ∉ E := by
  obtain ⟨E', hEE', hE', hz⟩ := exists_measurable_superset_of_null hzero
  have hsections : ∀ᵐ t ∂ν, τ ((fun q => (q, t)) ⁻¹' E') = 0 := by
    rw [Measure.prod_apply_symm hE'] at hz
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_right hE')).mp hz
  have hpair (k : ℕ) : ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod ν),
      (p.1.val.2 k, p.2) ∉ activeSlotParameterEvent E' := by
    have hm : MeasurableSet {p : BasePathCode d × T |
        (p.1.val.2 k, p.2) ∉ activeSlotParameterEvent E'} :=
      (measurableSet_activeSlotParameterEvent E' hE').compl.preimage
        (((measurable_pi_apply k).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_fst))).prodMk measurable_snd)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    have hreverse : ∀ᵐ t ∂ν, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        (Γ.val.2 k, t) ∉ activeSlotParameterEvent E' := by
      filter_upwards [hsections] with t ht
      filter_upwards [ae_active_slots_avoid d P τ hτ
        ((fun q => (q, t)) ⁻¹' E')
        (hE'.preimage (measurable_id.prodMk measurable_const)) ht] with Γ hΓ
      rintro ⟨q, hq, hqt⟩
      exact hΓ k q hq hqt
    exact (Measure.ae_ae_comm hm).mpr hreverse
  have hall := ae_all_iff.mpr hpair
  have hfull : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ t ∂ν,
      ∀ k, (Γ.val.2 k, t) ∉ activeSlotParameterEvent E' :=
    Measure.ae_ae_of_ae_prod hall
  filter_upwards [hfull] with Γ hΓ
  filter_upwards [hΓ] with t ht
  intro k q hq hmem
  exact ht k ⟨q, hq, hEE' hmem⟩

theorem ae_tag_contacts_singleton_at_independent_level
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set X) (hP : OrderedLevelNullCompatibility d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k q, Γ.val.2 k = Sum.inr q → ∀ t,
        tagLeft (Sum.inr q) < t → t < tagRight (Sum.inr q) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  have hg := ae_active_slots_avoid_independent_null d P (tupleReference ω) volume hτ
    {p | ¬ TuplePairCompatible d.levels Free p.1 (singleLevelTuple i p.2)}
    (tupleReference_single_level_incompatible_null d.levels Free hP ω i)
  filter_upwards [hg] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k q hq t hl hr hx hlevel
  have hcompat : TuplePairCompatible d.levels Free (tagDataTuple q) (singleLevelTuple i θ) :=
    not_not.mp (hθ k q hq)
  exact active_tag_singleton_at_compatible_level d.levels hH Free Γ.val.1 q
    (hq ▸ (Γ.property.1.2.1 k).1) (hq ▸ (Γ.property.1.2.1 k).2.1)
    t hl hr hx (hunique _ hx) i θ hlevel hcompat

end CircleDomainRigidity

end

end OAI
