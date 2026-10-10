import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafWork
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSnapshots

namespace OAI

/-! # Counted primitive structure operations of the representation reader

Replacement follows a single root-to-leaf path. Copying a snapshot instead
visits every mutable tree node. The immutable occurrence arrays are shared.
Counters below distinguish structural work from the cost of evaluating an
arbitrary supplied key; concrete indexed-mask key evaluation is charged by
the caller.
-/

namespace LowSpaceSubsetSum

namespace Tournament

variable {α : Type*}

/-- Rebuild one path, counting touched nodes. -/
def countedReplace (key : α → ℤ) : {d : ℕ} → Tree α d →
    (Fin d → Bool) → Option α → Tree α d × ℕ
  | 0, .leaf _, _, v => (.leaf v, 1)
  | _d + 1, .node _ l r, path, v =>
    if path 0 then
      let s := countedReplace key r (fun i => path i.succ) v
      (node key l s.1, s.2 + 1)
    else
      let s := countedReplace key l (fun i => path i.succ) v
      (node key s.1 r, s.2 + 1)

theorem countedReplace_value (key : α → ℤ) {d : ℕ} (t : Tree α d)
    (path : Fin d → Bool) (v : Option α) :
    (countedReplace key t path v).1 = replace key t path v := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr =>
    simp only [countedReplace, replace]
    split <;> simp only [ihl, ihr]

theorem countedReplace_nodes (key : α → ℤ) {d : ℕ} (t : Tree α d)
    (path : Fin d → Bool) (v : Option α) :
    (countedReplace key t path v).2 = d + 1 := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr =>
    simp only [countedReplace]
    split <;> simp only [ihl, ihr]

/-- A full snapshot copy, charged by the size of one node record. -/
def countedCopy (recordCells : ℕ) : {d : ℕ} → Tree α d → Tree α d × ℕ
  | 0, .leaf v => (.leaf v, recordCells)
  | _d + 1, .node w l r =>
    let a := countedCopy recordCells l
    let b := countedCopy recordCells r
    (.node w a.1 b.1, a.2 + b.2 + recordCells)

theorem countedCopy_value (recordCells : ℕ) {d : ℕ} (t : Tree α d) :
    (countedCopy recordCells t).1 = t := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr => simp only [countedCopy, ihl, ihr]

theorem countedCopy_cells (recordCells : ℕ) {d : ℕ} (t : Tree α d) :
    (countedCopy recordCells t).2 = recordCells * nodes t := by
  induction t with
  | leaf _ => simp only [countedCopy, nodes, Nat.mul_one]
  | node _ l r ihl ihr =>
    simp only [countedCopy, nodes, ihl, ihr]
    ring

end Tournament

namespace SliceCursor

variable {α : Type*}

/-- The three reader branches use no traversal of the backing array. The
nonempty branch performs one indexed load and one cyclic cursor update. -/
def countedNext (xs : Array α) (s : State xs.size) :
    Option (α × State xs.size) × ℕ :=
  match s.cursor with
  | none => (none, 2)
  | some c =>
    haveI : NeZero s.range.length := ⟨by have := c.position.isLt; omega⟩
    if c.remaining = 0 then (none, 4)
    else (some (values xs s.range c.position,
      ⟨s.range, some (CyclicCursor.advance c)⟩), 16)

theorem countedNext_value (xs : Array α) (s : State xs.size) :
    (countedNext xs s).1 = next xs s := by
  cases h : s.cursor with
  | none => simp only [countedNext, next, h]
  | some c => simp only [countedNext, next, h]; split <;> rfl

theorem countedNext_work (xs : Array α) (s : State xs.size) :
    (countedNext xs s).2 ≤ 16 := by
  unfold countedNext
  split
  · norm_num
  · split <;> norm_num

end SliceCursor

namespace PairCursor

variable {α β : Type*}

def countedNext (xs : Array β) (s : State α xs.size) :
    Option ((α × β) × State α xs.size) × ℕ :=
  let q := SliceCursor.countedNext xs s.cursor
  (q.1.map (fun z => ((s.left, z.1), ⟨s.left, z.2⟩)), q.2 + 4)

theorem countedNext_value (xs : Array β) (s : State α xs.size) :
    (countedNext xs s).1 = next xs s := by
  simp only [countedNext, SliceCursor.countedNext_value, next]

theorem countedNext_work (xs : Array β) (s : State α xs.size) :
    (countedNext xs s).2 ≤ 20 := by
  have h := SliceCursor.countedNext_work xs s.cursor
  change (SliceCursor.countedNext xs s.cursor).2 + 4 ≤ 20
  omega

end PairCursor

namespace FilteredStream

variable {α β : Type*}

def countedRead (right : Array β) : Cursor (α := α) right →
    Option ((α × β) × Cursor (α := α) right) × ℕ
  | none => (none, 2)
  | some s =>
    let q := PairCursor.countedNext right s
    (q.1.map (fun z => (z.1, some z.2)), q.2 + 4)

theorem countedRead_value (right : Array β) (s : Cursor (α := α) right) :
    (countedRead right s).1 = read right s := by
  cases s <;> simp only [countedRead, PairCursor.countedNext_value, read, PaddedRows.next]

theorem countedRead_work (right : Array β) (s : Cursor (α := α) right) :
    (countedRead right s).2 ≤ 24 := by
  cases s with
  | none => norm_num [countedRead]
  | some s =>
    have h := PairCursor.countedNext_work right s
    change (PairCursor.countedNext right s).2 + 4 ≤ 24
    omega

end FilteredStream

namespace RowMerge

variable {α σ : Type*} {d : ℕ}

/-- The same winning-row advance, with one counted row call and a counted
root path replacement. Eight units per visited node cover field access,
path tests, rebuilding and a cached comparison; key evaluation is separate. -/
def countedAdvance (key : α → ℤ) (read : σ → Option (α × σ) × ℕ)
    (t : Tournament.Tree (Front d α σ) d) :
    Option (α × Tournament.Tree (Front d α σ) d) × ℕ :=
  match Tournament.winner t with
  | none => (none, 2)
  | some x =>
    let q := read x.after
    let v := q.1.map (fun z => (⟨x.row, z.1, z.2⟩ : Front d α σ))
    let u := Tournament.countedReplace (fun y => key y.value) t x.row v
    (some (x.value, u.1), q.2 + 8 * u.2 + 8)

theorem countedAdvance_value (key : α → ℤ) (read : σ → Option (α × σ))
    (countedRead : σ → Option (α × σ) × ℕ) (hread : ∀ s, (countedRead s).1 = read s)
    (t : Tournament.Tree (Front d α σ) d) :
    (countedAdvance key countedRead t).1 = advance key read t := by
  unfold countedAdvance advance
  cases Tournament.winner t with
  | none => rfl
  | some x => simp only [Tournament.countedReplace_value, hread, front, Option.map_some]

theorem countedAdvance_work (key : α → ℤ) (read : σ → Option (α × σ) × ℕ)
    (K : ℕ) (hread : ∀ s, (read s).2 ≤ K)
    (t : Tournament.Tree (Front d α σ) d) :
    (countedAdvance key read t).2 ≤ K + 8 * (d + 1) + 8 := by
  unfold countedAdvance
  cases h : Tournament.winner t with
  | none => simp only; omega
  | some x =>
    simp only [Tournament.countedReplace_nodes]
    exact Nat.add_le_add_right (Nat.add_le_add_right (hread x.after) _) _

end RowMerge

namespace MergedReader

variable {α σ : Type*} {d : ℕ}

def countedNext (key : α → ℤ) (read : σ → Option (α × σ))
    (countedRead : σ → Option (α × σ) × ℕ) (hcount : ∀ s, (countedRead s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) : Option (α × State key view d) × ℕ :=
  let q := RowMerge.countedAdvance key countedRead s.tree
  match hq : q.1 with
  | none => (none, q.2)
  | some (a, t) =>
    have ha : RowMerge.advance key read s.tree = some (a, t) :=
      (RowMerge.countedAdvance_value key read countedRead hcount s.tree).symm.trans hq
    (some (a, ⟨t, RowMerge.advance_valid key read s.tree s.valid ha,
      RowMerge.advance_aligned key read s.tree s.aligned ha,
      advance_sorted key read view hread s ha⟩), q.2)

theorem countedNext_value (key : α → ℤ) (read : σ → Option (α × σ))
    (countedRead : σ → Option (α × σ) × ℕ) (hcount : ∀ s, (countedRead s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) :
    (countedNext key read countedRead hcount view hread s).1 = next key read view hread s := by
  unfold countedNext
  dsimp only
  split
  · rename_i hq
    exact (next_none key read view hread s
      ((RowMerge.countedAdvance_value key read countedRead hcount s.tree).symm.trans hq)).symm
  · rename_i a t hq
    exact (next_some key read view hread s
      ((RowMerge.countedAdvance_value key read countedRead hcount s.tree).symm.trans hq)).symm

theorem countedNext_work (key : α → ℤ) (read : σ → Option (α × σ))
    (countedRead : σ → Option (α × σ) × ℕ) (hcount : ∀ s, (countedRead s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) (K : ℕ) (hwork : ∀ s, (countedRead s).2 ≤ K) :
    (countedNext key read countedRead hcount view hread s).2 ≤ K + 8 * (d + 1) + 8 := by
  have hw := RowMerge.countedAdvance_work key countedRead K hwork s.tree
  unfold countedNext
  dsimp only
  split <;> exact hw

end MergedReader

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

def countedRead (s : D.State) :
    Option (RepresentationUniverse.ChildOccurrence (Fin n) × D.State) × ℕ :=
  MergedReader.countedNext
    (FilteredStream.key D.wl D.wl D.modulus D.mode)
    (FilteredStream.read D.storedRight) (FilteredStream.countedRead D.storedRight)
    (FilteredStream.countedRead_value D.storedRight)
    (FilteredStream.view D.storedRight) (FilteredStream.reader _) s

theorem countedRead_value (s : D.State) : (D.countedRead s).1 = D.read s :=
  MergedReader.countedNext_value _ _ _ _ _ _ _

theorem countedRead_work (s : D.State) (hL : D.leftArray.size ≤ 2 ^ n) :
    (D.countedRead s).2 ≤ 8 * n + 40 := by
  have hw := MergedReader.countedNext_work
    (FilteredStream.key D.wl D.wl D.modulus D.mode)
    (FilteredStream.read D.storedRight) (FilteredStream.countedRead D.storedRight)
    (FilteredStream.countedRead_value D.storedRight)
    (FilteredStream.view D.storedRight) (FilteredStream.reader _) s 24
    (FilteredStream.countedRead_work D.storedRight)
  have hd := Nat.clog_le_of_le_pow hL
  change (D.countedRead s).2 ≤ _ at hw
  omega

/-- Deep-copy the mutable reader tree while retaining the immutable array
parameters. The extra record allowance in `snapshotCells` covers the root. -/
def countedSnapshot (s : D.State) : D.State × ℕ :=
  let q := Tournament.countedCopy (12 * n + 32) s.tree
  have he : q.1 = s.tree := Tournament.countedCopy_value _ _
  (⟨q.1, he.symm ▸ s.valid, he.symm ▸ s.aligned, he.symm ▸ s.sorted⟩, q.2)

theorem countedSnapshot_value (s : D.State) : (D.countedSnapshot s).1 = s := by
  cases s
  simp only [countedSnapshot, Tournament.countedCopy_value]

theorem countedSnapshot_cells (s : D.State) :
    (D.countedSnapshot s).2 ≤ D.snapshotCells s := by
  simp only [countedSnapshot, Tournament.countedCopy_cells, snapshotCells]
  exact Nat.mul_le_mul_left _ (Nat.le_succ _)

end RepresentationPairData

end LowSpaceSubsetSum

end OAI
