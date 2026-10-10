import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredRestriction
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixExecution

namespace OAI

/-! # Prefix control executing bounded-list restriction updates

The collector receives the actual stored one/zero lists. Finite restrictions
appear only in the semantic refinement. The full traversal remains an
accounting object, while execution stops after the first accepting child.
-/

namespace LowSpaceSubsetSum.StoredPrefixController

variable {n : ℕ} {I : Instance n} {C : ℕ}

def header (n : ℕ) : ℕ := 20 * (n + 1) ^ 2 + 8

def run (collect : StoredRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ) :
    List (Fin n) → StoredRestriction n → Bool × ℕ
  | order, P =>
    let task := collect P
    if task.1.val.keys.overflow then
      match order with
      | [] => (false, task.2 + 4)
      | i :: rest =>
        let p₀ := P.force i false
        let left := run collect check rest p₀.1
        if left.1 then (true, task.2 + p₀.2 + left.2 + 6) else
          let p₁ := P.force i true
          let right := run collect check rest p₁.1
          (right.1, task.2 + p₀.2 + left.2 + p₁.2 + right.2 + 8)
    else
      let checked := check task.1.val.records
      (checked.1, task.2 + checked.2 + 4)

def fullCost (collect : StoredRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ) :
    List (Fin n) → StoredRestriction n → ℕ
  | order, P =>
    let task := collect P
    if task.1.val.keys.overflow then
      match order with
      | [] => task.2 + header n
      | i :: rest => task.2 + fullCost collect check rest (P.force i false).1 +
          fullCost collect check rest (P.force i true).1 + header n
    else task.2 + (check task.1.val.records).2 + header n

theorem run_work (collect : StoredRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ)
    (order : List (Fin n)) (P : StoredRestriction n) :
    (run collect check order P).2 ≤ fullCost collect check order P := by
  have hh : 8 ≤ header n := by unfold header; omega
  induction order generalizing P with
  | nil => simp only [run, fullCost]; split <;> omega
  | cons i order ih =>
    have hl := ih (P.force i false).1
    have hr := ih (P.force i true).1
    have hf₀ := P.force_work i false
    have hf₁ := P.force_work i true
    simp only [run, fullCost]
    split
    · split <;> dsimp only <;> unfold header at * <;> omega
    · omega

theorem run_value (D : RepresentationParentData n) (B : ℕ)
    (collect : StoredRestriction n → StoredEntry.Dictionary D.input D.capacity × ℕ)
    (hcollect : ∀ P, StoredDictionaryJoin.erase D.input D.capacity (collect P).1 =
      ({ D with maskRestriction := P.semantic }.collect B).state.user)
    (check : Array (StoredEntry n) → Bool × ℕ)
    (checkValue : Array (Entry (Fin n)) → Bool)
    (hcheck : ∀ a, (check a).1 = checkValue (a.map StoredEntry.semantic))
    (order : List (Fin n)) (P : StoredRestriction n) :
    (run collect check order P).1 = D.searchRight B checkValue order P.semantic := by
  have hk (P) := congrArg RecordedDictionary.State.keys (hcollect P)
  have hr (P) := congrArg RecordedDictionary.State.records (hcollect P)
  change ∀ P, (collect P).1.val.keys = _ at hk
  change ∀ P, (collect P).1.val.records.map StoredEntry.semantic = _ at hr
  induction order generalizing P with
  | nil =>
    simp only [run, RepresentationParentData.searchRight, hk, hcheck, hr]
    split <;> rfl
  | cons i order ih =>
    simp only [run, RepresentationParentData.searchRight, hk, hcheck, hr]
    split
    · simp only [ih, StoredRestriction.force_value]
      split <;> rfl
    · rfl

theorem fullCost_le_ledger (D : RepresentationParentData n) (B : ℕ)
    (collect : StoredRestriction n → StoredEntry.Dictionary D.input D.capacity × ℕ)
    (hcollect : ∀ P, StoredDictionaryJoin.erase D.input D.capacity (collect P).1 =
      ({ D with maskRestriction := P.semantic }.collect B).state.user)
    (check : Array (StoredEntry n) → Bool × ℕ) (A M R K W : ℕ)
    (hcheck : ∀ a, (check a).2 ≤ W)
    (hwork : ∀ P, (collect P).2 ≤ A * (D.capacity + 1) +
      M * (({ D with maskRestriction := P.semantic }).localLedger B).queries +
      R * (({ D with maskRestriction := P.semantic }).localLedger B).reports +
      K * (({ D with maskRestriction := P.semantic }).localLedger B).copies)
    (order : List (Fin n)) (P : StoredRestriction n) :
    fullCost collect check order P ≤
      (A * (D.capacity + 1) + header n) * D.taskStarts B order P.semantic +
      M * (D.prefixLedger B order P.semantic).queries +
      R * (D.prefixLedger B order P.semantic).reports +
      K * (D.prefixLedger B order P.semantic).copies +
      W * (D.completedArrays B order P.semantic).length := by
  have hk (P) := congrArg RecordedDictionary.State.keys (hcollect P)
  change ∀ P, (collect P).1.val.keys = _ at hk
  induction order generalizing P with
  | nil =>
    have hw := hwork P
    have hc := hcheck (collect P).1.val.records
    simp only [fullCost, hk, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split <;> simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_one]
    · omega
    · omega
  | cons i order ih =>
    have hw := hwork P
    have hc := hcheck (collect P).1.val.records
    have h₀ := ih (P.force i false).1
    have h₁ := ih (P.force i true).1
    simp only [StoredRestriction.force_value] at h₀ h₁
    simp only [fullCost, hk, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split
    · simp only [CompressionLedger.add, List.length_append, Nat.mul_add, Nat.mul_one]
      simp only [Nat.mul_add, Nat.mul_one] at hw h₀ h₁
      omega
    · simp only [List.length_nil, List.length_cons, Nat.mul_one]
      omega

end LowSpaceSubsetSum.StoredPrefixController

end OAI
