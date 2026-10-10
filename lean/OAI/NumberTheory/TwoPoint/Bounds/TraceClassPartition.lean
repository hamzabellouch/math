import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms

namespace OAI

/-! Partition the actual trace majorant into singleton, many-unlit, high-rank and good classes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem prohibited_trace_class_bound {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hdep : ∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) →
      weight a x = weight a y)
    (Smax Umax : ℕ) (rankBad : α → Finset (Fin R × Fin J) → Prop) :
    (∑ a ∈ F, |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤
      (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card),
        |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (fun U => Umax < U.card),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ Umax ∧ rankBad a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ Umax ∧ ¬rankBad a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) := by
  let A (a : α) := |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|
  let T (a : α) (U : Finset (Fin R × Fin J)) :=
    prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U
  have hp (a : α) : (∑ U ∈ (nonsingletonSlots (label a)).powerset, T a U) =
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (fun U => Umax < U.card), T a U) +
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ rankBad a U), T a U) +
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ ¬rankBad a U), T a U) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro U _
    by_cases hu : Umax < U.card <;> by_cases hr : rankBad a U
    · simp [hu, Nat.not_le.mpr hu]
    · simp [hu, Nat.not_le.mpr hu]
    · simp [hu, Nat.le_of_not_gt hu, hr]
    · simp [hu, Nat.le_of_not_gt hu, hr]
  change (∑ a ∈ F, A a) ≤ _
  calc
    _ = (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card), A a) +
        (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax), A a) := by
      rw [sum_filter, sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      by_cases ha : Smax < (singletonLabels (label a)).card
      · simp [ha, Nat.not_le.mpr ha]
      · simp [ha, Nat.le_of_not_gt ha]
    _ ≤ (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card), A a) +
        (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
          ∑ U ∈ (nonsingletonSlots (label a)).powerset, T a U) := by
      apply add_le_add_right
      apply sum_le_sum
      intro a ha
      exact prohibited_centering_bound data hB s D (word a) (label a) base
        (weight a) (hw a (mem_filter.mp ha).1) (hdep a (mem_filter.mp ha).1)
    _ = _ := by
      simp_rw [hp, sum_add_distrib]
      ring

end TwoPointCorrelations

end OAI
