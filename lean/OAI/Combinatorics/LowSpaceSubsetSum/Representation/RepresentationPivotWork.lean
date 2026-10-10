import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReaderWork

namespace OAI

/-! # Counted slice and modular-pivot initialization

Every nonempty row uses two primary-key searches and one modular-pivot
search. All three query the same immutable array; no slice is copied.
Predicate evaluation costs are separate from the number of queries.
-/

namespace LowSpaceSubsetSum

namespace BinarySlice

variable {α : Type*}

def countedRange (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    SliceCursor.Range xs.size × ℕ :=
  let lo := BinaryPivot.countedSearch (fun i : Fin xs.size => decide (key xs[i.val] < r)) k
  let hi := BinaryPivot.countedSearch (fun i : Fin xs.size => decide (key xs[i.val] ≤ r)) k
  have hlo : lo.1.lo = lower xs key r k :=
    congrArg BinaryPivot.Cut.lo (BinaryPivot.countedSearch_value _ _)
  have hhi : hi.1.lo = upper xs key r k :=
    congrArg BinaryPivot.Cut.lo (BinaryPivot.countedSearch_value _ _)
  (⟨lo.1.lo, hi.1.lo - lo.1.lo, by
      rw [hlo, hhi]
      exact (range xs key r k hs hk).bounded⟩,
    lo.2 + hi.2)

theorem countedRange_value (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    (countedRange xs key r k hs hk).1 = range xs key r k hs hk := by
  simp only [countedRange, BinaryPivot.countedSearch_value, lower, upper, range]

theorem countedRange_queries (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    (countedRange xs key r k hs hk).2 ≤ 2 * k := by
  have hl := BinaryPivot.countedSearch_queries
    (fun i : Fin xs.size => decide (key xs[i.val] < r)) k
  have hh := BinaryPivot.countedSearch_queries
    (fun i : Fin xs.size => decide (key xs[i.val] ≤ r)) k
  change _ + _ ≤ _
  omega

end BinarySlice

namespace ModularCursor

open scoped Fin.NatCast

variable {n : ℕ} [NeZero n] {α : Type*}

def countedForward (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    CyclicCursor.State n × ℕ :=
  let q := BinaryPivot.countedSearch (fun i => decide (residue (a i) < P - r)) k
  (⟨Fin.ofNat n q.1.lo, n, false⟩, q.2)

def countedReverse (a : Fin n → α) (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    CyclicCursor.State n × ℕ :=
  let q := BinaryPivot.countedSearch (fun i => decide (residue (a i) ≤ K)) k
  (⟨Fin.ofNat n q.1.lo - 1, n, true⟩, q.2)

theorem countedForward_value (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    (countedForward a residue P r k).1 = forwardStart a residue P r k := by
  simp only [countedForward, BinaryPivot.countedSearch_value, forwardStart]

theorem countedReverse_value (a : Fin n → α) (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    (countedReverse a residue K k).1 = reverseStart a residue K k := by
  simp only [countedReverse, BinaryPivot.countedSearch_value, reverseStart]

theorem countedForward_queries (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    (countedForward a residue P r k).2 ≤ k := BinaryPivot.countedSearch_queries _ _

theorem countedReverse_queries (a : Fin n → α) (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    (countedReverse a residue K k).2 ≤ k := BinaryPivot.countedSearch_queries _ _

end ModularCursor

namespace SliceModular

variable {α : Type*}

def countedForward (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) : SliceCursor.State xs.size × ℕ :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    let q := ModularCursor.countedForward (SliceCursor.values xs rr) residue P r k
    (⟨rr, some q.1⟩, q.2)
  else (⟨rr, none⟩, 0)

def countedReverse (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) : SliceCursor.State xs.size × ℕ :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    let q := ModularCursor.countedReverse (SliceCursor.values xs rr) residue K k
    (⟨rr, some q.1⟩, q.2)
  else (⟨rr, none⟩, 0)

theorem countedForward_value (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    (countedForward xs rr residue P r k).1 = forward xs rr residue P r k := by
  unfold countedForward forward
  split <;> simp only [ModularCursor.countedForward_value]

theorem countedReverse_value (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    (countedReverse xs rr residue K k).1 = reverse xs rr residue K k := by
  unfold countedReverse reverse
  split <;> simp only [ModularCursor.countedReverse_value]

theorem countedForward_queries (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    (countedForward xs rr residue P r k).2 ≤ k := by
  unfold countedForward
  split
  · rename_i h
    have : NeZero rr.length := ⟨by omega⟩
    exact ModularCursor.countedForward_queries _ _ _ _ _
  · exact Nat.zero_le _

theorem countedReverse_queries (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    (countedReverse xs rr residue K k).2 ≤ k := by
  unfold countedReverse
  split
  · rename_i h
    have : NeZero rr.length := ⟨by omega⟩
    exact ModularCursor.countedReverse_queries _ _ _ _
  · exact Nat.zero_le _

end SliceModular

namespace FilteredStream

variable {α β : Type*}

def countedRow (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) (x : α) :
    PairCursor.State α right.size × ℕ :=
  let k := steps right.size
  let rr := BinarySlice.countedRange right (fun y => wr y % p) ((c - wl x) % p)
    k hs (steps_sufficient right.size)
  let q := match mode with
    | .direct => SliceModular.countedForward right rr.1 (fun y => wr y % P) P (wl x % P) k
    | .complementary v =>
      SliceModular.countedReverse right rr.1 (fun y => wr y % P) ((v - wl x) % P) k
  (⟨x, q.1⟩, rr.2 + q.2)

theorem countedRow_value (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) (x : α) :
    (countedRow right wl wr p P c hs mode x).1 = row right wl wr p P c hs mode x := by
  cases mode <;> simp only [countedRow, row, FilteredRow.forward, FilteredRow.reverse,
    BinarySlice.countedRange_value, SliceModular.countedForward_value,
    SliceModular.countedReverse_value, FilteredRow.range]

theorem countedRow_queries (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) (x : α) :
    (countedRow right wl wr p P c hs mode x).2 ≤ 3 * steps right.size := by
  have hrr := BinarySlice.countedRange_queries right (fun y => wr y % p) ((c - wl x) % p)
    (steps right.size) hs (steps_sufficient right.size)
  let rr := (BinarySlice.countedRange right (fun y => wr y % p) ((c - wl x) % p)
    (steps right.size) hs (steps_sufficient right.size)).1
  cases mode with
  | direct =>
    have hq := SliceModular.countedForward_queries right rr (fun y => wr y % P) P
      (wl x % P) (steps right.size)
    change (BinarySlice.countedRange right (fun y => wr y % p) ((c - wl x) % p)
      (steps right.size) hs (steps_sufficient right.size)).2 +
        (SliceModular.countedForward right rr (fun y => wr y % P) P (wl x % P)
          (steps right.size)).2 ≤ _
    omega
  | complementary v =>
    have hq := SliceModular.countedReverse_queries right rr (fun y => wr y % P)
      ((v - wl x) % P) (steps right.size)
    change (BinarySlice.countedRange right (fun y => wr y % p) ((c - wl x) % p)
      (steps right.size) hs (steps_sufficient right.size)).2 +
        (SliceModular.countedReverse right rr (fun y => wr y % P) ((v - wl x) % P)
          (steps right.size)).2 ≤ _
    omega

theorem countedRow_index_queries (right : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right wr p) (mode : Mode) (x : α)
    (n : ℕ) (hn : right.size ≤ 2 ^ n) :
    (countedRow right wl wr p P c hs mode x).2 ≤ 3 * (n + 1) :=
  (countedRow_queries right wl wr p P c hs mode x).trans
    (Nat.mul_le_mul_left 3 (steps_le_index_bits right.size n hn))

end FilteredStream

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem schedule_countedSnapshot_cells (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    ∀ s : D.State, (D.countedSnapshot s).2 ≤ representationBufferCapacity n := by
  dsimp only
  let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
  intro s
  exact (D.countedSnapshot_cells s).trans
    (R.schedule_snapshotCells_le_buffer h r hn hlog hscale q hq z side P child s)

end RepresentationSetup
end LowSpaceSubsetSum

end OAI
