import OAI.Analysis.CircleDomains.Topology.RankedTagTopology
import OAI.Analysis.CircleDomains.Selection.IndependentTagLevel

namespace OAI

/-! Independent-level tag estimates in the inherited coordinate order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity

theorem active_tag_singleton_at_ranked_level
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (Free : Set X) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (hx : γ t ∈ Free)
    (hunique : ∀ i a b, (a, γ t) ∈ H i → (b, γ t) ∈ H i → a = b)
    (i : ℕ) (θ : UnitAddCircle) (hθ : (θ, γ t) ∈ H i)
    (hc : RankedTuplePairCompatible rank H Free (tagDataTuple q) (singleLevelTuple i θ)) :
    ¬ (connectedComponentIn {x | (θ, x) ∈ H i} (γ t)).Nontrivial := by
  intro hnt
  apply tag_impossible_below_ranked_level rank H hH γ q hshape hcontain t hl hr i
  · intro k hk
    rcases lt_trichotomy (rank (q.2.1 k)) (rank i) with hlt | he | hgt
    · exact hlt
    · have hei := hrank he
      have heq : q.2.2.1 k = θ := hunique i _ _ (hei ▸ hk) hθ
      exact (hc.1 k 0 hei heq).elim
    · have hh := hc.2.2 k (Finset.univ : Finset (Fin 1))
        (fun _ _ => hgt) (γ t) hx hk
      apply False.elim
      have hset : (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) =
          {y | (θ, y) ∈ H i} := by
        ext y
        constructor
        · intro hy
          obtain ⟨_, _, hy⟩ := mem_iUnion₂.mp hy
          exact hy
        · intro hy
          exact mem_iUnion₂.mpr ⟨0, Finset.mem_univ _, hy⟩
      change ¬ (connectedComponentIn
        (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) (γ t)).Nontrivial at hh
      rw [hset] at hh
      exact hh hnt
  · intro A hA
    exact hc.2.1 0 A hA (γ t) hx hθ

theorem tupleReference_ranked_single_level_incompatible_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    {X : Type*} [TopologicalSpace X]
    (H : ℕ → Set (UnitAddCircle × X)) (Free : Set X)
    (hP : RankedLevelNullCompatibility rank H Free)
    (ω : TupleType → ℝ≥0∞) (i : ℕ) :
    ((tupleReference ω).prod (volume : Measure UnitAddCircle))
      {p | ¬ RankedTuplePairCompatible rank H Free p.1 (singleLevelTuple i p.2)} = 0 := by
  apply tupleReference_product_right_null
  intro q
  let r : TupleType := ⟨0, fun _ => i⟩
  have hleft := ae_ranked_finite_tuple_ordered_compatibility rank H Free hP q.2 r.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_ranked_finite_tuple_ordered_compatibility rank H Free hP r.2 q.2)
  have hg : ∀ᵐ p ∂((volume : Measure (Fin (q.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin 1 → UnitAddCircle))),
      RankedTuplePairCompatible rank H Free (tupleFiber q p.1) (tupleFiber r p.2) := by
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

theorem ae_ranked_tag_contacts_singleton_at_independent_level
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set X) (hP : RankedLevelNullCompatibility rank d.levels Free)
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
    {p | ¬ RankedTuplePairCompatible rank d.levels Free p.1 (singleLevelTuple i p.2)}
    (tupleReference_ranked_single_level_incompatible_null rank d.levels Free hP ω i)
  filter_upwards [hg] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k q hq t hl hr hx hlevel
  have hcompat : RankedTuplePairCompatible rank d.levels Free (tagDataTuple q) (singleLevelTuple i θ) :=
    not_not.mp (hθ k q hq)
  exact active_tag_singleton_at_ranked_level rank hrank d.levels hH Free Γ.val.1 q
    (hq ▸ (Γ.property.1.2.1 k).1) (hq ▸ (Γ.property.1.2.1 k).2.1)
    t hl hr hx (hunique _ hx) i θ hlevel hcompat


end CircleDomainRigidity

end

end OAI
