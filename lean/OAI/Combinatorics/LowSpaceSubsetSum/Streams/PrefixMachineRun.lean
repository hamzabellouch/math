import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixMachine
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixTaskCount
import OAI.Combinatorics.LowSpaceSubsetSum.Search.WatchdogRanking

namespace OAI

/-! # Termination of the explicit prefix stack

The rank charges all possible task starts, including the sibling skipped
after an early YES. The stack machine terminates in at most three times
this task count plus two control actions. A collector action is a macro,
whose internal primitive operations still need their own watchdog.
-/

namespace LowSpaceSubsetSum.PrefixMachine

variable {n : ℕ}

def pendingWeight (D : RepresentationParentData n) (B : ℕ) (pending : List (Job n)) : ℕ :=
  (pending.map (fun job => 3 * D.taskStarts B job.order job.restriction + 2)).sum

def rank (D : RepresentationParentData n) (B : ℕ) : Control n → ℕ
  | .eval job pending =>
    3 * D.taskStarts B job.order job.restriction + pendingWeight D B pending + 2
  | .ret _ pending => pendingWeight D B pending + 1

theorem rank_pos (D : RepresentationParentData n) (B : ℕ) (s : Control n) :
    1 ≤ rank D B s := by cases s <;> simp only [rank] <;> omega

theorem rank_next (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (s t : Control n)
    (ht : step D B check s = .next t) : rank D B t < rank D B s := by
  cases s with
  | eval job pending =>
    cases job with
    | mk order P =>
      by_cases ho : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = true
      · cases order with
        | nil =>
          simp only [step, ho, ↓reduceIte] at ht
          cases ht
          simp only [rank, RepresentationParentData.taskStarts]
          omega
        | cons i rest =>
          simp only [step, ho, ↓reduceIte] at ht
          cases ht
          simp only [rank, pendingWeight, List.map_cons, List.sum_cons,
            RepresentationParentData.taskStarts, ho, ↓reduceIte]
          omega
      · have hf : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = false :=
          Bool.eq_false_iff.mpr ho
        simp only [step, hf, Bool.false_eq_true, ↓reduceIte] at ht
        cases ht
        cases order <;>
          simp only [rank, RepresentationParentData.taskStarts, hf, Bool.false_eq_true, ↓reduceIte] <;>
          omega
  | ret b pending =>
    cases b with
    | true => simp [step] at ht
    | false =>
      cases pending with
      | nil => simp [step] at ht
      | cons job pending =>
        simp only [step] at ht
        cases ht
        simp only [rank, pendingWeight, List.map_cons, List.sum_cons]
        omega

/-- The explicit stack performs exactly the original prefix search. -/
theorem output_eq_searchRight (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (job : Job n) :
    (Watchdog.run (step D B check) Control.cells
      (3 * D.taskStarts B job.order job.restriction + 2) (.eval job [])).output =
        some (D.searchRight B check job.order job.restriction) := by
  have h := Watchdog.ranked_complete (step D B check) Control.cells (rank D B)
    (rank_pos D B) (rank_next D B check) (meaning D B check) (fun s => by
      have hs := step_meaning D B check s
      cases ht : step D B check s <;> simp only [ht] at hs ⊢ <;> exact hs)
    (.eval job []) (3 * D.taskStarts B job.order job.restriction + 2)
    (by simp [rank, pendingWeight])
  simpa only [meaning, List.any_nil, Bool.or_false, jobValue] using h

end LowSpaceSubsetSum.PrefixMachine

end OAI
