import OAI.Analysis.CircleDomains.Topology.RankedTagTopology
import OAI.Analysis.CircleDomains.Selection.TagPairAvoidance

namespace OAI

/-! Independent active tags do not meet at free points when their labels
are compared in the inherited order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_ranked_no_tag_pair_contact
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d e : PathCodeData X Y) (hle : e.levels = d.levels)
    (hH : ∀ i, IsClosed (d.levels i)) (F : Set X)
    (hP : RankedLevelNullCompatibility rank d.levels F)
    (hunique : ∀ x ∈ F, ∀ i a b, (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτP : meanCodeTuple d P ≪ tupleReference ω)
    (hτQ : meanCodeTuple e Q ≪ tupleReference ω) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ k l t u, tagLeft (p.1.val.2 k) < t → t < tagRight (p.1.val.2 k) →
        tagLeft (p.2.val.2 l) < u → u < tagRight (p.2.val.2 l) →
        p.1.val.1 t ∈ F → p.2.val.1 u ≠ p.1.val.1 t := by
  have hnull := tupleReference_ranked_pair_incompatible_null rank d.levels F hP ω
  filter_upwards [ae_slot_pair_avoids_product_null d e P Q (tupleReference ω) hτP hτQ
    {p | ¬ RankedTuplePairCompatible rank d.levels F p.1 p.2} hnull] with p hp
  intro k l t u htl htr hul hur hx heq
  cases hq : p.1.val.2 k with
  | inl a =>
    simp only [hq, tagLeft, Sum.elim_inl] at htl
    exact not_lt_of_ge le_top htl
  | inr q =>
    cases hr : p.2.val.2 l with
    | inl a =>
      simp only [hr, tagLeft, Sum.elim_inl] at hul
      exact not_lt_of_ge le_top hul
    | inr r =>
      have hc : RankedTuplePairCompatible rank d.levels F (tagDataTuple q) (tagDataTuple r) :=
        not_not.mp (hp k l q r hq hr)
      have hrc : (p.2.val.1, (Sum.inr r : TagSlot)) ∈ tagContainment d.levels := by
        rw [← hle]
        exact hr ▸ (p.2.property.1.2.1 l).2.1
      apply incompatible_ranked_tag_pair_at_point rank hrank d.levels hH p.1.val.1 p.2.val.1 q r
        (hq ▸ (p.1.property.1.2.1 k).1) (hr ▸ (p.2.property.1.2.1 l).1)
        (hq ▸ (p.1.property.1.2.1 k).2.1)
        hrc
        t u (hq ▸ htl) (hq ▸ htr) (hr ▸ hul) (hr ▸ hur) heq
        (hunique _ hx) hc.1
      · intro j hj A hA
        exact hc.2.1 j A hA _ hx hj
      · intro i hi A hA
        exact hc.2.2 i A hA _ (heq ▸ hx) hi


end CircleDomainRigidity

end

end OAI
