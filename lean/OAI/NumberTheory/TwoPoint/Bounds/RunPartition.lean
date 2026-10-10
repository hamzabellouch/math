import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace OAI

/-! Cutting a compressed perfect block into regular segments and omitted runs. -/

namespace TwoPointCorrelations

variable {α : Type*}

/-- Omitted labels stand alone; consecutive regular labels form one segment. -/
def partitionColumnRuns (omitted : α → Bool) : List α → List (List α ⊕ α)
  | [] => []
  | a :: rest =>
      if omitted a then .inr a :: partitionColumnRuns omitted rest
      else match partitionColumnRuns omitted rest with
        | .inl segment :: tail => .inl (a :: segment) :: tail
        | tail => .inl [a] :: tail

/-- Cutting does not reorder, omit or duplicate any compressed run. -/
theorem partitionColumnRuns_flatten (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton) = runs := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha, List.singleton] using congrArg (List.cons a) ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simpa [partitionColumnRuns, ha, ht] using congrArg (List.cons a) ih
          | cons head tail =>
              cases head <;> simpa [partitionColumnRuns, ha, ht] using congrArg (List.cons a) ih

/-- The omitted part is exactly the original subsequence of omitted runs. -/
theorem partitionColumnRuns_omitted (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).filterMap (Sum.elim (fun _ => none) some) =
      runs.filter omitted := by
  induction runs with
  | nil => rfl
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha, List.filterMap_cons, Sum.elim] using
          congrArg (List.cons a) ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simpa [partitionColumnRuns, ha, ht, List.filterMap_cons, Sum.elim] using ih
          | cons head tail =>
              cases head <;> simpa [partitionColumnRuns, ha, ht, List.filterMap_cons, Sum.elim] using ih

/-- A merge mask needs no more slots than the compressed run list. -/
theorem partitionColumnRuns_length_le (omitted : α → Bool) (runs : List α) :
    (partitionColumnRuns omitted runs).length ≤ runs.length := by
  induction runs with
  | nil => simp [partitionColumnRuns]
  | cons a rest ih =>
      cases ha : omitted a with
      | true => simpa [partitionColumnRuns, ha] using Nat.succ_le_succ ih
      | false =>
          cases ht : partitionColumnRuns omitted rest with
          | nil => simp [partitionColumnRuns, ha, ht]
          | cons head tail =>
              cases head with
              | inl segment =>
                  simp only [ht, List.length_cons] at ih
                  simpa [partitionColumnRuns, ha, ht] using ih.trans (Nat.le_succ _)
              | inr label => simpa [partitionColumnRuns, ha, ht] using Nat.succ_le_succ ih

def regularPieceCount (pieces : List (List α ⊕ α)) : ℕ :=
  (pieces.filterMap (Sum.elim some (fun _ => none))).length

def omittedPieceCount (pieces : List (List α ⊕ α)) : ℕ :=
  (pieces.filterMap (Sum.elim (fun _ => none) some)).length

def startsWithRegularPiece (pieces : List (List α ⊕ α)) : Bool :=
  (pieces.head?.map (Sum.elim (fun _ => true) (fun _ => false))).getD false

/-- Every regular segment except a possible initial one is charged to an
omitted run. The stronger head-sensitive form makes the induction exact. -/
theorem partitionColumnRuns_count_strong (omitted : α → Bool) (runs : List α) :
    regularPieceCount (partitionColumnRuns omitted runs) ≤
      omittedPieceCount (partitionColumnRuns omitted runs) +
        if startsWithRegularPiece (partitionColumnRuns omitted runs) then 1 else 0 := by
  induction runs with
  | nil => simp [partitionColumnRuns, regularPieceCount, omittedPieceCount, startsWithRegularPiece]
  | cons a rest ih =>
      cases ht : partitionColumnRuns omitted rest with
      | nil =>
          cases ha : omitted a <;>
            simp [partitionColumnRuns, ha, ht, regularPieceCount, omittedPieceCount,
              startsWithRegularPiece, List.filterMap_cons, Sum.elim]
      | cons head tail =>
          cases head <;> cases ha : omitted a <;>
            simp [partitionColumnRuns, ha, ht, regularPieceCount, omittedPieceCount,
              startsWithRegularPiece, List.filterMap_cons, Sum.elim] at ih ⊢ <;> omega

theorem partitionColumnRuns_regular_count (omitted : α → Bool) (runs : List α) :
    regularPieceCount (partitionColumnRuns omitted runs) ≤ (runs.filter omitted).length + 1 := by
  have h := partitionColumnRuns_count_strong omitted runs
  have ho : omittedPieceCount (partitionColumnRuns omitted runs) = (runs.filter omitted).length := by
    exact congrArg List.length (partitionColumnRuns_omitted omitted runs)
  rw [ho] at h
  split_ifs at h <;> omega

end TwoPointCorrelations

end OAI
