import OAI.NumberTheory.TwoPoint.Bounds.TraceClassPartition

namespace OAI

/-! Combine the four estimates on one literal word catalog.  The bad classes
may be estimated on the larger catalog before the earlier restrictions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem prohibited_trace_four_bounds {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hdep : ∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) →
      weight a x = weight a y)
    (Smax Umax : ℕ) (rankBad : α → Finset (Fin R × Fin J) → Prop)
    (single unlit rank good : ℝ)
    (hsingle : (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card),
      |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤ single)
    (hunlit : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => Umax < U.card),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ unlit)
    (hrank : (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (rankBad a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ rank)
    (hgood : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ ¬rankBad a U),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ good) :
    (∑ a ∈ F, |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤
      single + unlit + rank + good := by
  have hnonneg (a : α) (ha : a ∈ F) (U : Finset (Fin R × Fin J)) :
      0 ≤ prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U :=
    prohibitedDesignatedTerm_nonneg data hB s D (word a) (label a) base (weight a) (hw a ha) U
  have hr : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ rankBad a U),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ rank := by
    apply le_trans _ hrank
    calc
      _ ≤ ∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
          ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (rankBad a),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum_of_subset_of_nonneg
        · intro U hU
          exact mem_filter.mpr ⟨(mem_filter.mp hU).1, (mem_filter.mp hU).2.2⟩
        · intro U _ _
          exact hnonneg a (mem_filter.mp ha).1 U
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro a ha _
        exact sum_nonneg (fun U _ => hnonneg a ha U)
  exact (prohibited_trace_class_bound data hB s D F word label base weight hw hdep
    Smax Umax rankBad).trans (add_le_add (add_le_add (add_le_add hsingle hunlit) hr) hgood)

end TwoPointCorrelations

end OAI
