import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredParentExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedPrefixSearch

namespace OAI

/-! # Depth-first prefix execution retaining bounded stored records

The collector result is inspected in place. Overflow discards it before either
recursive child is entered; an accepting first child skips the second child.
Only the proof view maps the stored masks to finite sets.
-/

namespace LowSpaceSubsetSum.StoredPrefixExecution

variable {n : ℕ} {I : Instance n} {C : ℕ}

def run (collect : MaskRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ) (H : ℕ) :
    List (Fin n) → MaskRestriction n → Bool × ℕ
  | order, P =>
    let task := collect P
    if task.1.val.keys.overflow then
      match order with
      | [] => (false, task.2 + H)
      | i :: rest =>
        let left := run collect check H rest (P.force i false)
        if left.1 then (true, task.2 + left.2 + H) else
          let right := run collect check H rest (P.force i true)
          (right.1, task.2 + left.2 + right.2 + H)
    else
      let checked := check task.1.val.records
      (checked.1, task.2 + checked.2 + H)

def fullCost (collect : MaskRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ) (H : ℕ) :
    List (Fin n) → MaskRestriction n → ℕ
  | order, P =>
    let task := collect P
    if task.1.val.keys.overflow then
      match order with
      | [] => task.2 + H
      | i :: rest => task.2 + fullCost collect check H rest (P.force i false) +
          fullCost collect check H rest (P.force i true) + H
    else task.2 + (check task.1.val.records).2 + H

theorem run_work (collect : MaskRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → Bool × ℕ) (H : ℕ)
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

theorem run_value (D : RepresentationParentData n) (B : ℕ)
    (collect : MaskRestriction n → StoredEntry.Dictionary D.input D.capacity × ℕ)
    (hcollect : ∀ P, StoredDictionaryJoin.erase D.input D.capacity (collect P).1 =
      ({ D with maskRestriction := P }.collect B).state.user)
    (check : Array (StoredEntry n) → Bool × ℕ)
    (checkValue : Array (Entry (Fin n)) → Bool)
    (hcheck : ∀ a, (check a).1 = checkValue (a.map StoredEntry.semantic))
    (H : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    (run collect check H order P).1 = D.searchRight B checkValue order P := by
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
    · simp only [ih]
      split <;> rfl
    · rfl

theorem fullCost_le_ledger (D : RepresentationParentData n) (B : ℕ)
    (collect : MaskRestriction n → StoredEntry.Dictionary D.input D.capacity × ℕ)
    (hcollect : ∀ P, StoredDictionaryJoin.erase D.input D.capacity (collect P).1 =
      ({ D with maskRestriction := P }.collect B).state.user)
    (check : Array (StoredEntry n) → Bool × ℕ) (H A M R K W : ℕ)
    (hcheck : ∀ a, (check a).2 ≤ W)
    (hwork : ∀ P, (collect P).2 ≤ A * (D.capacity + 1) +
      M * (({ D with maskRestriction := P }).localLedger B).queries +
      R * (({ D with maskRestriction := P }).localLedger B).reports +
      K * (({ D with maskRestriction := P }).localLedger B).copies)
    (order : List (Fin n)) (P : MaskRestriction n) :
    fullCost collect check H order P ≤
      (A * (D.capacity + 1) + H) * D.taskStarts B order P +
      M * (D.prefixLedger B order P).queries +
      R * (D.prefixLedger B order P).reports +
      K * (D.prefixLedger B order P).copies +
      W * (D.completedArrays B order P).length := by
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
    have h₀ := ih (P.force i false)
    have h₁ := ih (P.force i true)
    simp only [fullCost, hk, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split
    · simp only [CompressionLedger.add, List.length_append, Nat.mul_add, Nat.mul_one]
      simp only [Nat.mul_add, Nat.mul_one] at hw h₀ h₁
      omega
    · simp only [List.length_nil, List.length_cons, Nat.mul_one]
      omega

def taskCollector (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : MaskRestriction n) :
    StoredEntry.Dictionary D.input D.capacity × ℕ :=
  let out := StoredParentExecution.collect { D with maskRestriction := P } F hF B
  (out.1.state.user, out.2)

theorem taskCollector_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : MaskRestriction n) :
    StoredDictionaryJoin.erase D.input D.capacity (taskCollector D F hF B P).1 =
      ({ D with maskRestriction := P }.collect B).state.user := by
  exact congrArg (fun x : StreamJoin.StoppedResult
      ({ D with maskRestriction := P }.pair 0).State
      ({ D with maskRestriction := P }.pair 1).State
      (RecordedDictionary.State (Entry (Fin n))) => x.state.user)
    (StoredParentExecution.collect_value { D with maskRestriction := P } F hF B)

theorem taskCollector_work (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : MaskRestriction n) (hn : 10000 ≤ n)
    (hd₀ : Nat.clog 2 ({ D with maskRestriction := P }.pair 0).leftArray.size ≤ n)
    (hd₁ : Nat.clog 2 ({ D with maskRestriction := P }.pair 1).leftArray.size ≤ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({ D with maskRestriction := P }.pair 1).leftArray.size + 1) ≤ B) :
    (taskCollector D F hF B P).2 ≤ inputScale D.input ^ 6 * (D.capacity + 1) +
      inputScale D.input ^ 6 * ({ D with maskRestriction := P }.localLedger B).queries +
      inputScale D.input ^ 6 * ({ D with maskRestriction := P }.localLedger B).reports +
      B * ({ D with maskRestriction := P }.localLedger B).copies := by
  have hw := StoredParentExecution.collect_work { D with maskRestriction := P }
    F hF B hn hd₀ hd₁ hcopy
  change (taskCollector D F hF B P).2 ≤ _ at hw
  simp only [Nat.mul_add, Nat.mul_one] at hw ⊢
  change (taskCollector D F hF B P).2 ≤ _
  dsimp only [RepresentationParentData.localLedger]
  omega

theorem run_tasks_work (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n)
    (hdepth : ∀ P j, Nat.clog 2 ({ D with maskRestriction := P }.pair j).leftArray.size ≤ n)
    (hcopy : ∀ P, (12 * n + 32) *
      2 ^ (Nat.clog 2 ({ D with maskRestriction := P }.pair 1).leftArray.size + 1) ≤ B)
    (check : Array (StoredEntry n) → Bool × ℕ) (W : ℕ)
    (hcheck : ∀ a, (check a).2 ≤ W) (H : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n) :
    (run (taskCollector D F hF B) check H order P).2 ≤
      (inputScale D.input ^ 6 * (D.capacity + 1) + H) * D.taskStarts B order P +
      inputScale D.input ^ 6 * (D.prefixLedger B order P).queries +
      inputScale D.input ^ 6 * (D.prefixLedger B order P).reports +
      B * (D.prefixLedger B order P).copies +
      W * (D.completedArrays B order P).length := by
  apply (run_work _ _ _ _ _).trans
  exact fullCost_le_ledger D B _ (taskCollector_value D F hF B) check H
    (inputScale D.input ^ 6) (inputScale D.input ^ 6) (inputScale D.input ^ 6) B W hcheck
    (fun P => taskCollector_work D F hF B P hn (hdepth P 0) (hdepth P 1) (hcopy P))
    order P

end LowSpaceSubsetSum.StoredPrefixExecution

end OAI
