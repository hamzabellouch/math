import OAI.Analysis.CircleDomains.Topology.DomainPathAdmissibility
import OAI.Analysis.CircleDomains.Selection.NarrowedTagRules

namespace OAI

/-! A simple arc in a permitted finite level union can use one tag on its
whole open parameter interval. If its endpoints are in the domain, no dust
time remains and every residual constraint is vacuous. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def fullIntervalTag (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (levels : Fin (n + 1) → UnitAddCircle) : TagSlot :=
  Sum.inr ⟨n, labels, levels, ⊥, ⊤⟩

def fullIntervalTaggedPath {X : Type*} [TopologicalSpace X]
    (γ : C(PathTime, X)) (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (levels : Fin (n + 1) → UnitAddCircle) : TaggedPath X :=
  (γ, fun k => if k = 0 then fullIntervalTag n labels levels else inactiveTag)

theorem fullIntervalTag_rules {X : Type*} [MetricSpace X]
    (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hinj : Injective γ)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀ t, ∃ i, (levels i, γ t) ∈ H (labels i)) :
    TagRules H N (fullIntervalTaggedPath γ n labels levels) := by
  intro k
  by_cases hk : k = 0
  · subst k
    change (γ, fullIntervalTag n labels levels) ∈ validTagShape ∧
      (γ, fullIntervalTag n labels levels) ∈ tagContainment H ∧
      fullIntervalTag n labels levels ∉ tagTupleExcluded N
    refine ⟨Or.inr ?_, ?_, ?_⟩
    · let s : PathTime := ⟨1 / 3, by constructor <;> norm_num⟩
      let t : PathTime := ⟨2 / 3, by constructor <;> norm_num⟩
      refine ⟨s, t, ?_, ?_, ?_, ?_, ?_⟩
      · change (0 : ℝ) < 1 / 3; norm_num
      · change (1 / 3 : ℝ) < 1; norm_num
      · change (0 : ℝ) < 2 / 3; norm_num
      · change (2 / 3 : ℝ) < 1; norm_num
      · intro heq
        have := congrArg Subtype.val (hinj heq)
        norm_num [s, t] at this
    · intro t _ _
      exact hlevel t
    · exact fun h => hN ((active_mem_tagTupleExcluded_iff N _).mp h)
  · simpa only [fullIntervalTaggedPath, hk, ite_false] using inactiveTag_rules H N γ

theorem residualTimes_fullIntervalTaggedPath {X : Type*} [TopologicalSpace X]
    {B : Set X} (γ : C(PathTime, X))
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (h0 : γ ⊥ ∉ B) (h1 : γ ⊤ ∉ B) :
    residualTimes B (fullIntervalTaggedPath γ n labels levels) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨htB, ht⟩
  change γ t ∈ B at htB
  have ht0 := ht 0
  change t ≤ (⊥ : PathTime) ∨ (⊤ : PathTime) ≤ t at ht0
  rcases ht0 with ht0 | ht1
  · exact h0 (by simpa only [le_bot_iff.mp ht0] using htB)
  · exact h1 (by simpa only [top_le_iff.mp ht1] using htB)

theorem residualConstraintFamily_of_empty {X Z : Type*} [MetricSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] {B : Set X} {Γ : TaggedPath X}
    (h : residualTimes B Γ = ∅) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞) :
    ResidualConstraintFamily B R P ν m Γ := by
  intro i n a b
  unfold ResidualIncidenceBound
  have he : {z | (Γ, z) ∈ residualIncidence B (Icc a.toTime b.toTime) (R i) (P i n)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨t, ht, _⟩
    rw [h] at ht
    exact ht
  rw [he, measure_empty]
  exact bot_le

theorem fullIntervalTaggedPath_allowed {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hinj : Injective γ)
    (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀ t, ∃ i, (levels i, γ t) ∈ d.levels (labels i))
    (h0 : γ ⊥ ∉ d.dust) (h1 : γ ⊤ ∉ d.dust) :
    AllowedTaggedPath d ν N (fullIntervalTaggedPath γ n labels levels) := by
  have he := residualTimes_fullIntervalTaggedPath γ n labels levels h0 h1
  refine ⟨hfin, fullIntervalTag_rules d.levels N γ hinj n labels levels hN hlevel,
    residualConstraintFamily_of_empty he _ _ _ _,
    residualConstraintFamily_of_empty he _ _ _ _, ?_⟩
  rw [residualImage, he, image_empty, measure_empty]

end CircleDomainRigidity

end

end OAI
