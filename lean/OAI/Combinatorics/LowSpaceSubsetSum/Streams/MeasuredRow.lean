import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredPivot
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeys

namespace OAI

/-! # Modular row initialization with measured weight evaluation

Every binary-search predicate executes the stored-record weight routine.
The left weight is computed once, and all searches address the shared right
array directly. The resulting cursor is the original filtered row cursor.
-/

namespace LowSpaceSubsetSum
namespace BinarySlice

variable {α : Type*}

def measuredRange (xs : Array α) (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1))
    (hk : xs.size < 2 ^ k) : SliceCursor.Range xs.size × ℕ :=
  let lo := BinaryPivot.measuredSearch (fun i : Fin xs.size =>
    let q := key xs[i.val]; (decide (q.1 < r), q.2 + 2)) k
  let hi := BinaryPivot.measuredSearch (fun i : Fin xs.size =>
    let q := key xs[i.val]; (decide (q.1 ≤ r), q.2 + 2)) k
  have hlo : lo.1.lo = lower xs (fun x => (key x).1) r k :=
    congrArg BinaryPivot.Cut.lo (BinaryPivot.measuredSearch_value _ _)
  have hhi : hi.1.lo = upper xs (fun x => (key x).1) r k :=
    congrArg BinaryPivot.Cut.lo (BinaryPivot.measuredSearch_value _ _)
  (⟨lo.1.lo, hi.1.lo - lo.1.lo, by
    rw [hlo, hhi]
    exact (range xs (fun x => (key x).1) r k hs hk).bounded⟩,
    lo.2 + hi.2 + 4)

theorem measuredRange_value (xs : Array α) (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1))
    (hk : xs.size < 2 ^ k) :
    (measuredRange xs key r k hs hk).1 = range xs (fun x => (key x).1) r k hs hk := by
  simp only [measuredRange, BinaryPivot.measuredSearch_value, range, lower, upper]

theorem measuredRange_work (xs : Array α) (key : α → ℤ × ℕ) (r : ℤ) (k K : ℕ)
    (hkey : ∀ x, (key x).2 ≤ K)
    (hs : Monotone (fun i : Fin xs.size => (key xs[i.val]).1))
    (hk : xs.size < 2 ^ k) :
    (measuredRange xs key r k hs hk).2 ≤ 2 * (K + 10) * k + 4 := by
  have hl := BinaryPivot.measuredSearch_work
    (fun i : Fin xs.size => let q := key xs[i.val]; (decide (q.1 < r), q.2 + 2))
    (K + 2) (fun i => Nat.add_le_add_right (hkey xs[i.val]) 2) k
  have hh := BinaryPivot.measuredSearch_work
    (fun i : Fin xs.size => let q := key xs[i.val]; (decide (q.1 ≤ r), q.2 + 2))
    (K + 2) (fun i => Nat.add_le_add_right (hkey xs[i.val]) 2) k
  change _ + _ + 4 ≤ _
  simp only [Nat.add_assoc, Nat.mul_assoc, Nat.reduceAdd] at hl hh ⊢
  omega

end BinarySlice
namespace ModularCursor

open scoped Fin.NatCast

variable {n : ℕ} [NeZero n] {α : Type*}

def measuredForward (a : Fin n → α) (key : α → ℤ × ℕ) (P r : ℤ) (k : ℕ) :
    CyclicCursor.State n × ℕ :=
  let q := BinaryPivot.measuredSearch (fun i =>
    let w := key (a i); (decide (w.1 < P - r), w.2 + 2)) k
  (⟨Fin.ofNat n q.1.lo, n, false⟩, q.2 + 6)

def measuredReverse (a : Fin n → α) (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ) :
    CyclicCursor.State n × ℕ :=
  let q := BinaryPivot.measuredSearch (fun i =>
    let w := key (a i); (decide (w.1 ≤ r), w.2 + 2)) k
  (⟨Fin.ofNat n q.1.lo - 1, n, true⟩, q.2 + 6)

theorem measuredForward_value (a : Fin n → α) (key : α → ℤ × ℕ) (P r : ℤ) (k : ℕ) :
    (measuredForward a key P r k).1 = forwardStart a (fun x => (key x).1) P r k := by
  simp only [measuredForward, BinaryPivot.measuredSearch_value, forwardStart]

theorem measuredReverse_value (a : Fin n → α) (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ) :
    (measuredReverse a key r k).1 = reverseStart a (fun x => (key x).1) r k := by
  simp only [measuredReverse, BinaryPivot.measuredSearch_value, reverseStart]

theorem measuredForward_work (a : Fin n → α) (key : α → ℤ × ℕ) (P r : ℤ) (k K : ℕ)
    (hkey : ∀ x, (key x).2 ≤ K) :
    (measuredForward a key P r k).2 ≤ (K + 10) * k + 6 := by
  exact Nat.add_le_add_right (BinaryPivot.measuredSearch_work _ (K + 2)
    (fun i => Nat.add_le_add_right (hkey (a i)) 2) k) 6

theorem measuredReverse_work (a : Fin n → α) (key : α → ℤ × ℕ) (r : ℤ) (k K : ℕ)
    (hkey : ∀ x, (key x).2 ≤ K) :
    (measuredReverse a key r k).2 ≤ (K + 10) * k + 6 := by
  exact Nat.add_le_add_right (BinaryPivot.measuredSearch_work _ (K + 2)
    (fun i => Nat.add_le_add_right (hkey (a i)) 2) k) 6

end ModularCursor
namespace SliceModular

variable {α : Type*}

def measuredForward (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (P r : ℤ) (k : ℕ) : SliceCursor.State xs.size × ℕ :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    let q := ModularCursor.measuredForward (SliceCursor.values xs rr) key P r k
    (⟨rr, some q.1⟩, q.2 + 2)
  else (⟨rr, none⟩, 1)

def measuredReverse (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ) : SliceCursor.State xs.size × ℕ :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    let q := ModularCursor.measuredReverse (SliceCursor.values xs rr) key r k
    (⟨rr, some q.1⟩, q.2 + 2)
  else (⟨rr, none⟩, 1)

theorem measuredForward_value (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (P r : ℤ) (k : ℕ) :
    (measuredForward xs rr key P r k).1 = forward xs rr (fun x => (key x).1) P r k := by
  unfold measuredForward forward
  split <;> simp only [ModularCursor.measuredForward_value]

theorem measuredReverse_value (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (r : ℤ) (k : ℕ) :
    (measuredReverse xs rr key r k).1 = reverse xs rr (fun x => (key x).1) r k := by
  unfold measuredReverse reverse
  split <;> simp only [ModularCursor.measuredReverse_value]

theorem measuredForward_work (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (P r : ℤ) (k K : ℕ) (hkey : ∀ x, (key x).2 ≤ K) :
    (measuredForward xs rr key P r k).2 ≤ (K + 10) * k + 8 := by
  unfold measuredForward
  split
  · rename_i h
    have : NeZero rr.length := ⟨by omega⟩
    exact Nat.add_le_add_right (ModularCursor.measuredForward_work _ key P r k K hkey) 2
  · omega

theorem measuredReverse_work (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : α → ℤ × ℕ) (r : ℤ) (k K : ℕ) (hkey : ∀ x, (key x).2 ≤ K) :
    (measuredReverse xs rr key r k).2 ≤ (K + 10) * k + 8 := by
  unfold measuredReverse
  split
  · rename_i h
    have : NeZero rr.length := ⟨by omega⟩
    exact Nat.add_le_add_right (ModularCursor.measuredReverse_work _ key r k K hkey) 2
  · omega

end SliceModular
end LowSpaceSubsetSum
namespace LowSpaceSubsetSum.FilteredStream

variable {α β : Type*}

def measuredRow (right : Array β) (wl : α → ℤ × ℕ) (wr : β → ℤ × ℕ)
    (p P c : ℤ) (hs : FilteredRow.PrimarySorted right (fun y => (wr y).1) p)
    (mode : Mode) (x : α) : PairCursor.State α right.size × ℕ :=
  let wx := wl x
  let k := steps right.size
  let low := fun y => let w := wr y; (w.1 % p, w.2 + 2)
  let high := fun y => let w := wr y; (w.1 % P, w.2 + 2)
  let rr := BinarySlice.measuredRange right low ((c - wx.1) % p) k
    hs (steps_sufficient right.size)
  let q := match mode with
    | .direct => SliceModular.measuredForward right rr.1 high P (wx.1 % P) k
    | .complementary v => SliceModular.measuredReverse right rr.1 high ((v - wx.1) % P) k
  (⟨x, q.1⟩, wx.2 + rr.2 + q.2 + 4)

theorem measuredRow_value (right : Array β) (wl : α → ℤ × ℕ) (wr : β → ℤ × ℕ)
    (p P c : ℤ) (hs : FilteredRow.PrimarySorted right (fun y => (wr y).1) p)
    (mode : Mode) (x : α) :
    (measuredRow right wl wr p P c hs mode x).1 =
      row right (fun x => (wl x).1) (fun y => (wr y).1) p P c hs mode x := by
  cases mode <;> simp only [measuredRow, row, FilteredRow.forward, FilteredRow.reverse,
    BinarySlice.measuredRange_value, SliceModular.measuredForward_value,
    SliceModular.measuredReverse_value, FilteredRow.range]

theorem measuredRow_work (right : Array β) (wl : α → ℤ × ℕ) (wr : β → ℤ × ℕ)
    (p P c : ℤ) (hs : FilteredRow.PrimarySorted right (fun y => (wr y).1) p)
    (mode : Mode) (x : α) (K : ℕ)
    (hl : ∀ x, (wl x).2 ≤ K) (hr : ∀ y, (wr y).2 ≤ K) :
    (measuredRow right wl wr p P c hs mode x).2 ≤
      3 * (K + 12) * steps right.size + K + 16 := by
  let low := fun y => let w := wr y; (w.1 % p, w.2 + 2)
  let high := fun y => let w := wr y; (w.1 % P, w.2 + 2)
  let k := steps right.size
  let rr := BinarySlice.measuredRange right low ((c - (wl x).1) % p) k
    hs (steps_sufficient right.size)
  have hrr := BinarySlice.measuredRange_work right low ((c - (wl x).1) % p) k (K + 2)
    (fun y => Nat.add_le_add_right (hr y) 2) hs (steps_sufficient right.size)
  have hx := hl x
  cases mode with
  | direct =>
    have hq := SliceModular.measuredForward_work right rr.1 high P ((wl x).1 % P) k
      (K + 2) (fun y => Nat.add_le_add_right (hr y) 2)
    change (wl x).2 + rr.2 +
      (SliceModular.measuredForward right rr.1 high P ((wl x).1 % P) k).2 + 4 ≤ _
    change rr.2 ≤ 2 * (K + 2 + 10) * k + 4 at hrr
    change _ ≤ 3 * (K + 12) * k + K + 16
    simp only [Nat.add_assoc, Nat.mul_assoc, Nat.reduceAdd] at hrr hq ⊢
    omega
  | complementary v =>
    have hq := SliceModular.measuredReverse_work right rr.1 high ((v - (wl x).1) % P) k
      (K + 2) (fun y => Nat.add_le_add_right (hr y) 2)
    change (wl x).2 + rr.2 +
      (SliceModular.measuredReverse right rr.1 high ((v - (wl x).1) % P) k).2 + 4 ≤ _
    change rr.2 ≤ 2 * (K + 2 + 10) * k + 4 at hrr
    change _ ≤ 3 * (K + 12) * k + K + 16
    simp only [Nat.add_assoc, Nat.mul_assoc, Nat.reduceAdd] at hrr hq ⊢
    omega

end LowSpaceSubsetSum.FilteredStream

end OAI
