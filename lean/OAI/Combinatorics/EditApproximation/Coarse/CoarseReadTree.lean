import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedRead

namespace OAI

namespace EditApproximation

/-- A source descriptor is expanded by index arithmetic. No sliced or padded
list is allocated. The function is the original stored input's read operation. -/
def coarseReadTree (B : ℕ) {α : Type*} :
    (d : ℕ) → (ℕ → Option α) → CoarseSourceTree B α d
  | 0, read => .leaf (read 0)
  | d + 1, read => .branch (fun i =>
      coarseReadTree B d (fun j => read (i.val * B ^ d + j)))

theorem coarseReadTree_ext (B d : ℕ) {α : Type*} (read other : ℕ → Option α)
    (heq : ∀ i < B ^ d, read i = other i) :
    coarseReadTree B d read = coarseReadTree B d other := by
  induction d generalizing read other with
  | zero => exact congrArg CoarseSourceTree.leaf (heq 0 (by simp))
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    apply ih
    intro j hj
    apply heq
    rw [pow_succ]
    have hmul := Nat.mul_le_mul_right (B ^ d) (Nat.succ_le_of_lt i.isLt)
    have hpos : 0 < B ^ d := by omega
    nlinarith

theorem coarseReadTree_list (B d : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[i]?) = coarseSourceTreeOfList B d source := by
  induction d generalizing source with
  | zero => simp only [coarseReadTree, coarseSourceTreeOfList, List.head?_eq_getElem?]
  | succ d ih =>
    apply congrArg CoarseSourceTree.branch
    funext i
    rw [← ih]
    apply coarseReadTree_ext
    intro j hj
    simp only [List.getElem?_take_of_lt hj, List.getElem?_drop, Nat.add_comm]

theorem coarseReadTree_shift (B d start : ℕ) {α : Type*} (source : List α) :
    coarseReadTree B d (fun i => source[start + i]?) =
      coarseSourceTreeOfList B d (source.drop start) := by
  rw [← coarseReadTree_list]
  congr 1
  funext i
  simp only [List.getElem?_drop]

theorem coarseReadTree_shift_length (B d start : ℕ) {α : Type*} (source : List α) :
    (coarseReadTree B d (fun i => source[start + i]?)).word.length =
      min (B ^ d) (source.length - start) := by
  rw [coarseReadTree_shift, coarseSourceTreeOfList_word, List.length_take, List.length_drop]

/-- Cached length of a descriptor into a virtually padded source. -/
def coarseDescriptorLength (B d n start : ℕ) : ℕ := min (B ^ d) (n - start)

theorem coarseReadTree_padded_length (B d n start : ℕ) {α : Type*}
    (source : List α) (hn : source.length ≤ n) :
    (coarseReadTree B d (fun i => coarsePaddedRead n source (start + i))).word.length =
      coarseDescriptorLength B d n start := by
  have heq : (fun i => coarsePaddedRead n source (start + i)) =
      (fun i => (coarsePadTo n source)[start + i]?) := by
    funext i
    exact coarsePaddedRead_value n source hn _
  rw [heq, coarseReadTree_shift_length, coarsePadTo_length n source hn]
  rfl

theorem coarseReadTree_entry (B d : ℕ) {α : Type*} (source target : List α) :
    coarseReadTree B d (coarsePaddedRead (coarseEntryWidth source target) source) =
      coarseEntryTree B d source target := by
  have heq : coarsePaddedRead (coarseEntryWidth source target) source =
      (fun i => (coarsePadTo (coarseEntryWidth source target) source)[i]?) := by
    funext i
    exact coarsePaddedRead_value _ _ (le_max_left _ _) i
  rw [heq, coarseReadTree_list]
  rfl

end EditApproximation

end OAI
