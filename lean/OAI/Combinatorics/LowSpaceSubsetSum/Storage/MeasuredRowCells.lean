import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredPivotCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRecordInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells

namespace OAI

/-! # Explicit scratch for the three searches initializing a stored row

Range endpoints and modular pivots use tail binary search on the retained
right array. Only one weight evaluation is live at any time.
-/

namespace LowSpaceSubsetSum.MeasuredRowCells

variable {α : Type*}

def range (xs : Array α) (key : α → (ℤ × ℕ) × ℕ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1.1))
    (hk : xs.size < 2 ^ k) : (SliceCursor.Range xs.size × ℕ) × ℕ :=
  let lo := MeasuredPivotCells.search (fun i : Fin xs.size =>
    let q := key xs[i.val]; ((decide (q.1.1 < r), q.1.2 + 2), q.2 + 8)) k
  let hi := MeasuredPivotCells.search (fun i : Fin xs.size =>
    let q := key xs[i.val]; ((decide (q.1.1 ≤ r), q.1.2 + 2), q.2 + 8)) k
  have hlo : lo.1.1.lo = BinarySlice.lower xs (fun x => (key x).1.1) r k := by
    simp only [lo, MeasuredPivotCells.search_value, BinarySlice.lower,
      BinaryPivot.measuredSearch_value]
  have hhi : hi.1.1.lo = BinarySlice.upper xs (fun x => (key x).1.1) r k := by
    simp only [hi, MeasuredPivotCells.search_value, BinarySlice.upper,
      BinaryPivot.measuredSearch_value]
  ((⟨lo.1.1.lo, hi.1.1.lo - lo.1.1.lo, by
    rw [hlo, hhi]
    exact (BinarySlice.range xs (fun x => (key x).1.1) r k hs hk).bounded⟩,
      lo.1.2 + hi.1.2 + 4), max lo.2 hi.2 + 24)

theorem range_value (xs : Array α) (key : α → (ℤ × ℕ) × ℕ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1.1)) (hk : xs.size < 2 ^ k) :
    (range xs key r k hs hk).1 = BinarySlice.measuredRange xs (fun x => (key x).1) r k hs hk := by
  simp only [range, BinarySlice.measuredRange, MeasuredPivotCells.search_value]

theorem range_cells (xs : Array α) (key : α → (ℤ × ℕ) × ℕ) (r : ℤ) (k R : ℕ)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1.1)) (hk : xs.size < 2 ^ k)
    (hr : ∀ x, (key x).2 ≤ R) : (range xs key r k hs hk).2 ≤ R + 72 := by
  have hl := MeasuredPivotCells.search_cells (fun i : Fin xs.size =>
    let q := key xs[i.val]; ((decide (q.1.1 < r), q.1.2 + 2), q.2 + 8)) (R + 8)
    (fun i => Nat.add_le_add_right (hr xs[i.val]) 8) k
  have hh := MeasuredPivotCells.search_cells (fun i : Fin xs.size =>
    let q := key xs[i.val]; ((decide (q.1.1 ≤ r), q.1.2 + 2), q.2 + 8)) (R + 8)
    (fun i => Nat.add_le_add_right (hr xs[i.val]) 8) k
  change max _ _ + 24 ≤ _
  omega

def start (xs : Array α) (rr : SliceCursor.Range xs.size) (key : α → (ℤ × ℕ) × ℕ)
    (P r : ℤ) (k : ℕ) (reverse : Bool) : (SliceCursor.State xs.size × ℕ) × ℕ :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    let q := MeasuredPivotCells.search (fun i : Fin rr.length =>
      let w := key (SliceCursor.values xs rr i)
      ((if reverse then decide (w.1.1 ≤ r) else decide (w.1.1 < P - r), w.1.2 + 2), w.2 + 8)) k
    let pos := if reverse then Fin.ofNat rr.length q.1.1.lo - 1 else Fin.ofNat rr.length q.1.1.lo
    ((⟨rr, some ⟨pos, rr.length, reverse⟩⟩, q.1.2 + 8), q.2 + 32)
  else ((⟨rr, none⟩, 1), 16)

theorem start_value (xs : Array α) (rr : SliceCursor.Range xs.size) (key : α → (ℤ × ℕ) × ℕ)
    (P r : ℤ) (k : ℕ) (reverse : Bool) :
    (start xs rr key P r k reverse).1 =
      if reverse then SliceModular.measuredReverse xs rr (fun x => (key x).1) r k
      else SliceModular.measuredForward xs rr (fun x => (key x).1) P r k := by
  cases reverse <;>
    simp only [start, Bool.false_eq_true, ↓reduceIte, SliceModular.measuredForward,
      SliceModular.measuredReverse, ModularCursor.measuredForward, ModularCursor.measuredReverse]
  all_goals split <;> simp only [MeasuredPivotCells.search_value]

theorem start_cells (xs : Array α) (rr : SliceCursor.Range xs.size) (key : α → (ℤ × ℕ) × ℕ)
    (P r : ℤ) (k R : ℕ) (reverse : Bool) (hr : ∀ x, (key x).2 ≤ R) :
    (start xs rr key P r k reverse).2 ≤ R + 80 := by
  unfold start
  split
  · rename_i h
    have : NeZero rr.length := ⟨by omega⟩
    have hh := MeasuredPivotCells.search_cells (fun i : Fin rr.length =>
      let w := key (SliceCursor.values xs rr i)
      ((if reverse then decide (w.1.1 ≤ r) else decide (w.1.1 < P - r), w.1.2 + 2), w.2 + 8))
      (R + 8) (fun i => Nat.add_le_add_right (hr (SliceCursor.values xs rr i)) 8) k
    dsimp only at hh ⊢
    omega
  · dsimp only; omega

variable {n : ℕ}

def row (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n)) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n) :
    (PairCursor.State (LeafRecord n) right.size × ℕ) × ℕ :=
  let wx := RepresentationKeyCells.leafWeight I F x
  let k := FilteredStream.steps right.size
  let low := fun y => let w := RepresentationKeyCells.leafWeight I F y
    ((w.1.1 % p, w.1.2 + 2), w.2 + 8)
  let high := fun y => let w := RepresentationKeyCells.leafWeight I F y
    ((w.1.1 % P, w.1.2 + 2), w.2 + 8)
  let rr := range right low ((c - wx.1.1) % p) k
    (by simpa only [low, FilteredRow.PrimarySorted, RepresentationKeyCells.leafWeight_value] using hs)
    (FilteredStream.steps_sufficient right.size)
  let q := match mode with
    | .direct => start right rr.1.1 high P (wx.1.1 % P) k false
    | .complementary v => start right rr.1.1 high P ((v - wx.1.1) % P) k true
  ((⟨x, q.1.1⟩, wx.1.2 + rr.1.2 + q.1.2 + 4), max wx.2 (max rr.2 q.2) + 3 * n + 68)

theorem row_value (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n)) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n) :
    (row I F right p P c hs mode x).1 = RepresentationKeys.row I F right p P c hs mode x := by
  cases mode <;>
    simp only [row, RepresentationKeys.row, FilteredStream.measuredRow,
      range_value, start_value, RepresentationKeyCells.leafWeight_value, Bool.false_eq_true, ↓reduceIte]

theorem row_cells (I : Instance n) (F : IndexedMask n) (right : Array (LeafRecord n)) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) (x : LeafRecord n) :
    (row I F right p P c hs mode x).2 ≤ 200 * inputScale I := by
  have hw := RepresentationKeyCells.leafWeight_cells I F x
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  let low := fun y => let w := RepresentationKeyCells.leafWeight I F y
    ((w.1.1 % p, w.1.2 + 2), w.2 + 8)
  let high := fun y => let w := RepresentationKeyCells.leafWeight I F y
    ((w.1.1 % P, w.1.2 + 2), w.2 + 8)
  have hh : ∀ y, (high y).2 ≤ 12 * n + 32 := by
    intro y
    exact Nat.add_le_add_right (RepresentationKeyCells.leafWeight_cells I F y) 8
  have hl : ∀ y, (low y).2 ≤ 12 * n + 32 := by
    intro y
    exact Nat.add_le_add_right (RepresentationKeyCells.leafWeight_cells I F y) 8
  let k := FilteredStream.steps right.size
  let rr := range right low ((c - (RepresentationKeyCells.leafWeight I F x).1.1) % p) k
    (by simpa only [low, FilteredRow.PrimarySorted, RepresentationKeyCells.leafWeight_value] using hs)
    (FilteredStream.steps_sufficient right.size)
  have hr := range_cells right low ((c - (RepresentationKeyCells.leafWeight I F x).1.1) % p)
    k (12 * n + 32)
    (by simpa only [low, FilteredRow.PrimarySorted, RepresentationKeyCells.leafWeight_value] using hs)
    (FilteredStream.steps_sufficient right.size) hl
  change rr.2 ≤ _ at hr
  cases mode with
  | direct =>
    have hq := start_cells right rr.1.1 high P ((RepresentationKeyCells.leafWeight I F x).1.1 % P)
      k (12 * n + 32) false hh
    change max (RepresentationKeyCells.leafWeight I F x).2
      (max rr.2 (start right rr.1.1 high P ((RepresentationKeyCells.leafWeight I F x).1.1 % P) k false).2) +
        3 * n + 68 ≤ _
    omega
  | complementary v =>
    have hq := start_cells right rr.1.1 high P ((v - (RepresentationKeyCells.leafWeight I F x).1.1) % P)
      k (12 * n + 32) true hh
    change max (RepresentationKeyCells.leafWeight I F x).2
      (max rr.2 (start right rr.1.1 high P ((v - (RepresentationKeyCells.leafWeight I F x).1.1) % P) k true).2) +
        3 * n + 68 ≤ _
    omega

end LowSpaceSubsetSum.MeasuredRowCells

end OAI
