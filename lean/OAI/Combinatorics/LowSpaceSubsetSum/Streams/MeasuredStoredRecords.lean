import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredRecords

namespace OAI

/-! # Executed generation retaining bounded index lists

The subset generators return index lists. Wrapping them as bounded masks
retains those lists; finite sets occur only in the semantic specification.
The work counter includes wrapping and both Cartesian-product traversals.
-/

namespace LowSpaceSubsetSum
namespace IndexedMask

variable {n : ℕ}

private theorem selectedList_length (xs ys : List (Fin n)) (k : ℕ)
    (h : ys ∈ (CountedSubsets.select k xs).1) : ys.length ≤ xs.length := by
  rw [CountedSubsets.select_value] at h
  exact (List.mem_sublistsLen.mp h).1.length_le

private theorem allList_length (xs ys : List (Fin n))
    (h : ys ∈ (CountedSubsets.all xs).1) : ys.length ≤ xs.length := by
  rw [CountedSubsets.all_value] at h
  exact (List.mem_sublists.mp h).length_le

def measuredSelected (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    List (IndexedMask n) × ℕ :=
  let out := CountedSubsets.select k xs
  (out.1.attach.map (fun y => ⟨y.val,
    (selectedList_length xs y.val k y.property).trans hx⟩), out.2 + out.1.length)

def measuredAll (xs : List (Fin n)) (hx : xs.length ≤ n) : List (IndexedMask n) × ℕ :=
  let out := CountedSubsets.all xs
  (out.1.attach.map (fun y => ⟨y.val,
    (allList_length xs y.val y.property).trans hx⟩), out.2 + out.1.length)

@[simp] theorem measuredSelected_value (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    (measuredSelected xs hx k).1 = selected xs hx k := rfl

@[simp] theorem measuredAll_value (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (measuredAll xs hx).1 = all xs hx := rfl

@[simp] theorem selected_length (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    (selected xs hx k).length = xs.length.choose k := by
  simp only [selected, List.length_map, List.length_attach, CountedSubsets.select_length]

@[simp] theorem all_length (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (all xs hx).length = 2 ^ xs.length := by
  simp only [all, List.length_map, List.length_attach, CountedSubsets.all_length]

end IndexedMask

namespace RepresentationLeaf

variable {n : ℕ}

def measuredStoredRecords (L : RepresentationLeaf (Fin n)) : List (LeafRecord n) × ℕ :=
  if L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card then
    let dt := domainSort L.top
    let dm := domainSort L.mixer
    let db := domainSort L.background
    let t := IndexedMask.measuredSelected dt.1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.top) L.topCount
    let m := IndexedMask.measuredSelected dm.1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.mixer) L.localCount
    let b := IndexedMask.measuredAll db.1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.background)
    let tm := t.1 ×ˢ m.1
    let out := (tm ×ˢ b.1).map (fun y => (⟨y.1.1, y.1.2, y.2⟩ : LeafRecord n))
    (out, dt.2 + dm.2 + db.2 + t.2 + m.2 + b.2 +
      4 * tm.length + 8 * out.length + 3 * (n + 1))
  else ([], 3 * (n + 1))

theorem measuredStoredRecords_value (L : RepresentationLeaf (Fin n)) :
    L.measuredStoredRecords.1 = L.storedRecords := by
  simp only [measuredStoredRecords, storedRecords]
  split <;> simp only [IndexedMask.measuredSelected_value, IndexedMask.measuredAll_value]

theorem measuredStoredRecords_cost (L : RepresentationLeaf (Fin n)) :
    L.measuredStoredRecords.2 ≤ 3 * L.countedEnumerate.2 := by
  by_cases hf : L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card
  · have hc : 1 ≤ 2 ^ L.background.card := Nat.one_le_two_pow
    have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have htm : L.top.card.choose L.topCount * L.mixer.card.choose L.localCount ≤
        L.top.card.choose L.topCount * L.mixer.card.choose L.localCount *
          2 ^ L.background.card := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left
        (L.top.card.choose L.topCount * L.mixer.card.choose L.localCount) hc
    have hsum : L.top.card.choose L.topCount + L.mixer.card.choose L.localCount +
        2 ^ L.background.card ≤ (n + 1) ^ 2 *
        (L.top.card.choose L.topCount + L.mixer.card.choose L.localCount +
          2 ^ L.background.card) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right
        (L.top.card.choose L.topCount + L.mixer.card.choose L.localCount + 2 ^ L.background.card) hp
    simp only [measuredStoredRecords, countedEnumerate, ite_eq_left hf,
      IndexedMask.measuredSelected, IndexedMask.measuredAll, List.length_product,
      List.length_map, List.length_attach, CountedSubsets.select_length,
      CountedSubsets.all_length, domainSort_length]
    omega
  · simp only [measuredStoredRecords, countedEnumerate, ite_eq_right hf]
    omega

theorem measuredStoredRecords_work (L : RepresentationLeaf (Fin n)) :
    L.measuredStoredRecords.2 ≤ 192 * (n + 1) ^ 2 * (L.occurrences.card + 1) := by
  have h := Nat.mul_le_mul_left 3 L.countedEnumerate_work
  exact L.measuredStoredRecords_cost.trans (by nlinarith only [h])

theorem measuredStoredRecords_scale (I : Instance n) (L : RepresentationLeaf (Fin n))
    (hn : 10000 ≤ n) :
    L.measuredStoredRecords.2 ≤ inputScale I ^ 3 * (L.occurrences.card + 1) := by
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hs := Nat.pow_le_pow_left hnu 2
  have hm := Nat.mul_le_mul_right (inputScale I ^ 2)
    (show 192 ≤ inputScale I by omega)
  have hp : 192 * (n + 1) ^ 2 ≤ inputScale I ^ 3 := by nlinarith only [hs, hm]
  exact L.measuredStoredRecords_work.trans (Nat.mul_le_mul_right _ hp)

end RepresentationLeaf
end LowSpaceSubsetSum

end OAI
