import OAI.NumberTheory.TwoPoint.Bounds.RunPartition
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix

namespace OAI

/-! The omitted-label cut retains the actual adjacency of every regular segment. -/

namespace TwoPointCorrelations

variable {α β : Type*}

/-- Every regular piece is a contiguous part of the original run list. -/
theorem partitionColumnRuns_regular_infix (omitted : α → Bool) (runs segment : List α)
    (hsegment : Sum.inl segment ∈ partitionColumnRuns omitted runs) :
    segment.IsInfix runs := by
  have hm : segment ∈ (partitionColumnRuns omitted runs).map (Sum.elim id List.singleton) :=
    List.mem_map.mpr ⟨.inl segment, hsegment, rfl⟩
  have hi := List.infix_of_mem_flatten hm
  change segment.IsInfix ((partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton)) at hi
  rwa [partitionColumnRuns_flatten] at hi

/-- Cutting out omitted runs does not create new adjacent pairs inside a piece. -/
theorem partitionColumnRuns_regular_chain (R : α → α → Prop)
    (omitted : α → Bool) (runs segment : List α) (hchain : runs.IsChain R)
    (hsegment : Sum.inl segment ∈ partitionColumnRuns omitted runs) :
    segment.IsChain R :=
  hchain.infix (partitionColumnRuns_regular_infix omitted runs segment hsegment)

/-- The cut algorithm produces only nonempty regular pieces, all of whose
entries really are regular. -/
theorem partitionColumnRuns_regular_entries (omitted : α → Bool) (runs : List α) :
    ∀ segment, Sum.inl segment ∈ partitionColumnRuns omitted runs →
      segment ≠ [] ∧ ∀ a ∈ segment, omitted a = false := by
  induction runs with
  | nil => simp [partitionColumnRuns]
  | cons a rest ih =>
      intro segment hs
      cases ha : omitted a with
      | true =>
          simp only [partitionColumnRuns, ha, ↓reduceIte,
            List.mem_cons, Sum.inl_ne_inr, false_or] at hs
          exact ih segment hs
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil =>
              simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                List.mem_singleton, Sum.inl.injEq] at hs
              subst segment
              simp [ha]
          | cons head tail =>
              cases head with
              | inl old =>
                  have hold := ih old (by rw [ht]; simp)
                  simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                    List.mem_cons, Sum.inl.injEq] at hs
                  rcases hs with rfl | hs
                  · exact ⟨List.cons_ne_nil _ _, fun b hb => by
                      rcases List.mem_cons.mp hb with rfl | hb
                      · exact ha
                      · exact hold.2 b hb⟩
                  · exact ih segment (by rw [ht]; exact List.mem_cons_of_mem _ hs)
              | inr b =>
                  simp only [partitionColumnRuns, ha, Bool.false_eq_true, ↓reduceIte, ht,
                    List.mem_cons, Sum.inl.injEq, Sum.inl_ne_inr, false_or] at hs
                  rcases hs with rfl | hs
                  · simp [ha]
                  · exact ih segment (by rw [ht]; exact List.mem_cons_of_mem _ hs)

/-- Run positions and their labels may be cut in parallel: the algorithm
uses only the omitted predicate, so forgetting the positions commutes with it. -/
theorem partitionColumnRuns_map (f : α → β) (omitted : β → Bool) (runs : List α) :
    partitionColumnRuns omitted (runs.map f) =
      (partitionColumnRuns (fun a => omitted (f a)) runs).map (Sum.map (List.map f) f) := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted (f a) with
      | true => simpa [partitionColumnRuns, ha] using congrArg (List.cons (.inr (f a))) ih
      | false =>
          cases ht : partitionColumnRuns (fun a => omitted (f a)) rest with
          | nil => simp [partitionColumnRuns, ha, ht, ih]
          | cons head tail =>
              cases head <;> simp [partitionColumnRuns, ha, ht, ih, Sum.map]

end TwoPointCorrelations

end OAI
