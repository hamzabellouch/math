import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationJoinLedger
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixTaskCount

namespace OAI

/-! # Counted depth-first prefix execution

Only the current collector result survives until its overflow test or checker.
On overflow the result is discarded before entering either child. The full
cost tree is an analysis object; execution skips the second child after YES.
Collector and checker implementations carry their own internal costs.
-/

namespace LowSpaceSubsetSum.CountedPrefixSearch

variable {n : ℕ}

def run (collect : MaskRestriction n → RecordedDictionary.State (Entry (Fin n)) × ℕ)
    (check : Array (Entry (Fin n)) → Bool × ℕ) (H : ℕ) :
    List (Fin n) → MaskRestriction n → Bool × ℕ
  | order, P =>
    let task := collect P
    if task.1.keys.overflow then
      match order with
      | [] => (false, task.2 + H)
      | i :: rest =>
        let left := run collect check H rest (P.force i false)
        if left.1 then (true, task.2 + left.2 + H) else
          let right := run collect check H rest (P.force i true)
          (right.1, task.2 + left.2 + right.2 + H)
    else
      let checked := check task.1.records
      (checked.1, task.2 + checked.2 + H)

/-- The hypothetical full tree includes a sibling skipped after early YES. -/
def fullCost (collect : MaskRestriction n → RecordedDictionary.State (Entry (Fin n)) × ℕ)
    (check : Array (Entry (Fin n)) → Bool × ℕ) (H : ℕ) :
    List (Fin n) → MaskRestriction n → ℕ
  | order, P =>
    let task := collect P
    if task.1.keys.overflow then
      match order with
      | [] => task.2 + H
      | i :: rest => task.2 + fullCost collect check H rest (P.force i false) +
          fullCost collect check H rest (P.force i true) + H
    else task.2 + (check task.1.records).2 + H

theorem run_value (D : RepresentationParentData n) (B : ℕ)
    (collect : MaskRestriction n → RecordedDictionary.State (Entry (Fin n)) × ℕ)
    (hcollect : ∀ P, (collect P).1 = ({ D with maskRestriction := P }.collect B).state.user)
    (check : Array (Entry (Fin n)) → Bool × ℕ) (H : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) :
    (run collect check H order P).1 = D.searchRight B (fun a => (check a).1) order P := by
  induction order generalizing P with
  | nil =>
    simp only [run, RepresentationParentData.searchRight, hcollect]
    split <;> rfl
  | cons i order ih =>
    simp only [run, RepresentationParentData.searchRight, hcollect]
    split
    · simp only [ih]
      split <;> rfl
    · rfl

theorem run_work
    (collect : MaskRestriction n → RecordedDictionary.State (Entry (Fin n)) × ℕ)
    (check : Array (Entry (Fin n)) → Bool × ℕ) (H : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) :
    (run collect check H order P).2 ≤ fullCost collect check H order P := by
  induction order generalizing P with
  | nil => simp only [run, fullCost]; split <;> rfl
  | cons i order ih =>
    have hl := ih (P.force i false)
    have hr := ih (P.force i true)
    simp only [run, fullCost]
    split
    · split <;> dsimp only <;> omega
    · rfl

/-- Separate task setup, join counters and completed checker calls. This
composes concrete task cost proofs without revisiting the exponential tree. -/
theorem fullCost_le_ledger (D : RepresentationParentData n) (B : ℕ)
    (collect : MaskRestriction n → RecordedDictionary.State (Entry (Fin n)) × ℕ)
    (hcollect : ∀ P, (collect P).1 = ({ D with maskRestriction := P }.collect B).state.user)
    (check : Array (Entry (Fin n)) → Bool × ℕ) (H A M C K : ℕ)
    (hwork : ∀ P, (collect P).2 ≤ A * (D.capacity + 1) +
      M * (({ D with maskRestriction := P }).localLedger B).queries +
      C * (({ D with maskRestriction := P }).localLedger B).reports +
      K * (({ D with maskRestriction := P }).localLedger B).copies)
    (order : List (Fin n)) (P : MaskRestriction n) :
    fullCost collect check H order P ≤
      (A * (D.capacity + 1) + H) * D.taskStarts B order P +
      M * (D.prefixLedger B order P).queries +
      C * (D.prefixLedger B order P).reports +
      K * (D.prefixLedger B order P).copies +
      ((D.completedArrays B order P).map (fun a => (check a).2)).sum := by
  induction order generalizing P with
  | nil =>
    have hw := hwork P
    simp only [fullCost, hcollect, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split <;> simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
      Nat.add_zero, Nat.mul_one]
    · omega
    · omega
  | cons i order ih =>
    have hw := hwork P
    have h₀ := ih (P.force i false)
    have h₁ := ih (P.force i true)
    simp only [fullCost, hcollect, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split
    · simp only [CompressionLedger.add, Nat.mul_add, Nat.mul_one, List.map_append, List.sum_append]
      simp only [Nat.mul_add, Nat.mul_one] at hw h₀ h₁
      omega
    · simp only [Nat.mul_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

end LowSpaceSubsetSum.CountedPrefixSearch

end OAI
