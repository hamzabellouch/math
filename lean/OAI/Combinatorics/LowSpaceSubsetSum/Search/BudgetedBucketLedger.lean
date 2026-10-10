import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedBucket
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CheckListWork
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixTaskCount

namespace OAI

/-! # Charging the retained-array checks to the source prefix ledger -/

namespace LowSpaceSubsetSum.BudgetedBucketLedger

variable {n g : ℕ}

private theorem charge_reorder (a u s l t : ℕ) :
    a + u * (s + l * t) = a + u * l * t + u * s := by ring

private theorem list_bills (arrays : List (Array (Entry (Fin n))))
    (scans : Array (Entry (Fin n)) → ℕ) (K L C : ℕ)
    (hs : ∀ a ∈ arrays, a.size ≤ C + 1) :
    (arrays.map (fun a => K * (scans a + L + a.size + 1))).sum ≤
      K * ((arrays.map scans).sum + (L + C + 2) * arrays.length) := by
  induction arrays with
  | nil => simp
  | cons a arrays ih =>
    have ha := hs a (by simp)
    have ht := ih (fun b hb => hs b (by simp only [List.mem_cons]; exact Or.inr hb))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ K * (scans a + L + C + 2) +
          K * ((arrays.map scans).sum + (L + C + 2) * arrays.length) :=
        Nat.add_le_add (Nat.mul_le_mul_left K (by omega)) ht
      _ = _ := by ring

theorem completed_bills (D : RepresentationParentData n) (B : ℕ)
    (order : List (Fin n)) (P : MaskRestriction n)
    (scans : Array (Entry (Fin n)) → ℕ) (K L : ℕ) :
    ((D.completedArrays B order P).map
      (fun a => K * (scans a + L + a.size + 1))).sum ≤
      K * (((D.completedArrays B order P).map scans).sum +
        (L + D.capacity + 2) * D.taskStarts B order P) := by
  have hs : ∀ a ∈ D.completedArrays B order P, a.size ≤ D.capacity + 1 := by
    intro a ha
    obtain ⟨Q, _, rfl⟩ := D.mem_completedArrays B order P a ha
    exact ({D with maskRestriction := Q}.storage B).1
  exact (list_bills _ scans K L D.capacity hs).trans
    (Nat.mul_le_mul_left K (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (D.completedArrays_length_le B order P)) _))

noncomputable def semanticBill (D : RepresentationBucketData n g)
    (families : Fin 4 → Array (Finset (Fin g)))
    (left right : Array (Entry (Fin n))) : ℕ :=
  inputScale D.right.input ^ 6 *
    ((D.coordinates.check families D.target left.toList right.toList).scans +
      left.size + right.size + 1)

theorem checkBill_semantic (D : RepresentationBucketData n g)
    (families : Fin 4 → Array (Finset (Fin g))) (left right : Array (StoredEntry n)) :
    BudgetedPreparedBucket.checkBill D families left right =
      semanticBill D families (left.map StoredEntry.semantic) (right.map StoredEntry.semantic) := by
  simp only [BudgetedPreparedBucket.checkBill, semanticBill, Array.size_map]

theorem prefix_allowance (D : RepresentationBucketData n g) (F : IndexedMask n)
    (hF : F.semantic = D.right.signs) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) (left : Array (StoredEntry n)) :
    BudgetedConcretePrefix.allowance D.right F hF B
      (BudgetedPreparedBucket.checkBill D families left) D.topOrder StoredRestriction.empty ≤
      ((2 * inputScale D.right.input ^ 9 + inputScale D.right.input ^ 3 + 16) *
          (D.right.capacity + 1) + StoredPrefixController.header n) *
        D.right.taskStarts B D.topOrder MaskRestriction.empty +
      inputScale D.right.input ^ 7 *
        (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
      B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies +
      inputScale D.right.input ^ 6 *
        (((D.right.completedArrays B D.topOrder MaskRestriction.empty).map
          (fun right => (D.coordinates.check families D.target
            (left.map StoredEntry.semantic).toList right.toList).scans)).sum +
          (left.size + D.right.capacity + 2) *
            D.right.taskStarts B D.topOrder MaskRestriction.empty) := by
  have hp := BudgetedConcretePrefix.allowance_ledger D.right F hF B
    (BudgetedPreparedBucket.checkBill D families left)
    (semanticBill D families (left.map StoredEntry.semantic))
    (checkBill_semantic D families left) D.topOrder StoredRestriction.empty
  have hs := completed_bills D.right B D.topOrder MaskRestriction.empty
    (fun right => (D.coordinates.check families D.target
      (left.map StoredEntry.semantic).toList right.toList).scans)
    (inputScale D.right.input ^ 6) left.size
  have heq : semanticBill D families (left.map StoredEntry.semantic) =
      (fun a => inputScale D.right.input ^ 6 *
        ((D.coordinates.check families D.target
          (left.map StoredEntry.semantic).toList a.toList).scans + left.size + a.size + 1)) := by
    funext a
    simp only [semanticBill, Array.size_map]
  rw [heq] at hp
  simp only [StoredRestriction.empty_value] at hp
  exact hp.trans (Nat.add_le_add_left hs _)

noncomputable def prefixCharge (D : RepresentationBucketData n g) (B L : ℕ) : ℕ :=
  ((2 * inputScale D.right.input ^ 9 + inputScale D.right.input ^ 3 + 16) *
      (D.right.capacity + 1) + StoredPrefixController.header n) *
    D.right.taskStarts B D.topOrder MaskRestriction.empty +
  inputScale D.right.input ^ 7 *
    (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
  B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies +
  inputScale D.right.input ^ 6 * (L + D.right.capacity + 2) *
    D.right.taskStarts B D.topOrder MaskRestriction.empty

theorem allowance_ledger (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (hleft : D.left.maskRestriction = MaskRestriction.empty) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g))) :
    let left := (ComputedParentExecution.run D.left FL StoredRestriction.empty hFL B).1.dictionary
    BudgetedPreparedBucket.allowance D FL FR hFL hFR B families ≤
      8 + BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty +
        prefixCharge D B left.val.records.size + inputScale D.right.input ^ 6 *
          D.coordinates.totalScans families D.target (D.checkList B) := by
  dsimp only
  let left := (ComputedParentExecution.run D.left FL StoredRestriction.empty hFL B).1.dictionary
  change _ ≤ 8 + _ + prefixCharge D B left.val.records.size + _
  have he := ComputedParentExecution.dictionary_value D.left FL StoredRestriction.empty hFL B
  have hreset : {D.left with maskRestriction := MaskRestriction.empty} = D.left := by
    rw [← hleft]
  change StoredEntry.mapDictionary left.val =
    ({D.left with maskRestriction := MaskRestriction.empty}.collect B).state.user at he
  rw [hreset] at he
  have hk := congrArg RecordedDictionary.State.keys he
  have hr := congrArg RecordedDictionary.State.records he
  change left.val.keys = _ at hk
  change left.val.records.map StoredEntry.semantic = _ at hr
  change 8 + _ + (if left.val.keys.overflow || left.val.records.isEmpty then 0 else _) ≤ _
  by_cases hs : (left.val.keys.overflow || left.val.records.isEmpty) = true
  · rw [ite_eq_left hs]
    omega
  · rw [ite_eq_right hs]
    obtain ⟨ho, hi⟩ := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hs)
    have himap : (left.val.records.map StoredEntry.semantic).isEmpty = false := by
      simpa only [Array.isEmpty, Array.size_map] using hi
    have hscans :
        ((D.right.completedArrays B D.topOrder MaskRestriction.empty).map
          (fun right => (D.coordinates.check families D.target
            (left.val.records.map StoredEntry.semantic).toList right.toList).scans)).sum =
          D.coordinates.totalScans families D.target (D.checkList B) := by
      simp only [RepresentationBucketData.checkList, ← hk, ho, Bool.false_eq_true,
        ↓reduceIte, ← hr, himap, TopCoordinates.totalScans, List.map_map]
      rfl
    have hp := prefix_allowance D FR hFR B families left.val.records
    rw [hscans] at hp
    have hp' : BudgetedConcretePrefix.allowance D.right FR hFR B
        (BudgetedPreparedBucket.checkBill D families left.val.records) D.topOrder
        StoredRestriction.empty ≤ prefixCharge D B left.val.records.size +
          inputScale D.right.input ^ 6 * D.coordinates.totalScans families D.target (D.checkList B) := by
      change _ ≤
        (((2 * inputScale D.right.input ^ 9 + inputScale D.right.input ^ 3 + 16) *
          (D.right.capacity + 1) + StoredPrefixController.header n) *
          D.right.taskStarts B D.topOrder MaskRestriction.empty +
          inputScale D.right.input ^ 7 *
            (D.right.prefixLedger B D.topOrder MaskRestriction.empty).queries +
          B * (D.right.prefixLedger B D.topOrder MaskRestriction.empty).copies) +
        inputScale D.right.input ^ 6 * (left.val.records.size + D.right.capacity + 2) *
          D.right.taskStarts B D.topOrder MaskRestriction.empty +
        inputScale D.right.input ^ 6 * D.coordinates.totalScans families D.target (D.checkList B)
      exact hp.trans_eq (charge_reorder _ _ _ _ _)
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hp'
      (8 + BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty)

end LowSpaceSubsetSum.BudgetedBucketLedger

end OAI
