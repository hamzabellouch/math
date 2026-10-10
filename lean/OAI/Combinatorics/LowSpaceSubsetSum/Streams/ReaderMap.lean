import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredRecords

namespace OAI

/-! # Semantic maps for the mutable reader structures

Mapping records preserves the tournament paths and all cursor coordinates.
Immutable backing arrays are mapped once; they are not copied by a read.
-/

namespace LowSpaceSubsetSum

namespace Tournament

variable {α β : Type*}

def map (f : α → β) : {d : ℕ} → Tree α d → Tree β d
  | 0, .leaf v => .leaf (v.map f)
  | _d + 1, .node w l r => .node (w.map f) (map f l) (map f r)

@[simp] theorem winner_map (f : α → β) {d : ℕ} (t : Tree α d) :
    winner (map f t) = (winner t).map f := by cases t <;> rfl

@[simp] theorem nodes_map (f : α → β) {d : ℕ} (t : Tree α d) :
    nodes (map f t) = nodes t := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr => simp only [map, nodes, ihl, ihr]

theorem pick_map (f : α → β) (key : β → ℤ) (a b : Option α) :
    (pick (fun x => key (f x)) a b).map f = pick key (a.map f) (b.map f) := by
  cases a <;> cases b <;> simp only [pick, Option.map_none, Option.map_some]
  split <;> rfl

theorem node_map (f : α → β) (key : β → ℤ) {d : ℕ} (l r : Tree α d) :
    map f (node (fun x => key (f x)) l r) = node key (map f l) (map f r) := by
  simp only [node, map, pick_map, winner_map]

theorem valid_map (f : α → β) (key : β → ℤ) {d : ℕ} (t : Tree α d)
    (h : Valid (fun x => key (f x)) t) : Valid key (map f t) := by
  induction t with
  | leaf _ => trivial
  | node w l r ihl ihr =>
    refine ⟨?_, ihl h.2.1, ihr h.2.2⟩
    rw [h.1, pick_map, winner_map, winner_map]

theorem lookup_map (f : α → β) {d : ℕ} (t : Tree α d) (p : Fin d → Bool) :
    lookup (map f t) p = (lookup t p).map f := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr =>
    simp only [map, lookup]
    split <;> simp only [ihl, ihr]

theorem replace_map (f : α → β) (key : β → ℤ) {d : ℕ} (t : Tree α d)
    (p : Fin d → Bool) (v : Option α) :
    map f (replace (fun x => key (f x)) t p v) = replace key (map f t) p (v.map f) := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr =>
    simp only [map, replace]
    split <;> simp only [node_map, ihl, ihr]

theorem build_map (f : α → β) (key : β → ℤ) (d : ℕ)
    (front : (Fin d → Bool) → Option α) :
    map f (build (fun x => key (f x)) d front) =
      build key d (fun p => (front p).map f) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [build, node_map, ih]

end Tournament

namespace CyclicCursor

variable {α β : Type*} {n : ℕ} [NeZero n]

theorem trace_map (f : α → β) (a : Fin n → α) (k : ℕ) (c : State n) :
    (trace a k c).map f = trace (fun i => f (a i)) k c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [trace]
    split <;> simp only [List.map_nil, List.map_cons, ih]

end CyclicCursor

namespace SliceCursor

variable {α β : Type*}

def mapRange (f : α → β) (xs : Array α) (r : Range xs.size) : Range (xs.map f).size :=
  ⟨r.lo, r.length, by simpa using r.bounded⟩

def mapState (f : α → β) (xs : Array α) (s : State xs.size) : State (xs.map f).size :=
  ⟨mapRange f xs s.range, s.cursor⟩

theorem values_map (f : α → β) (xs : Array α) (r : Range xs.size) (i : Fin r.length) :
    values (xs.map f) (mapRange f xs r) i = f (values xs r i) := by
  simp only [values, mapRange, Array.getElem_map]

theorem next_map (f : α → β) (xs : Array α) (s : State xs.size) :
    (next xs s).map (fun z => (f z.1, mapState f xs z.2)) =
      next (xs.map f) (mapState f xs s) := by
  cases h : s.cursor with
  | none => simp only [next, mapState, h, Option.map_none]
  | some c =>
    simp only [next, mapState, h]
    split <;> simp only [Option.map_none, Option.map_some, values_map]
    rfl

theorem output_map (f : α → β) (xs : Array α) (s : State xs.size) :
    (output xs s).map f = output (xs.map f) (mapState f xs s) := by
  cases h : s.cursor with
  | none => simp only [output, mapState, h, List.map_nil]
  | some c =>
    have : NeZero s.range.length := ⟨by have := c.position.isLt; omega⟩
    simp only [output, mapState, h, CyclicCursor.trace_map]
    congr 1
    funext i
    exact (values_map f xs s.range i).symm

end SliceCursor

namespace PairCursor

variable {α β γ δ : Type*}

def mapState (f : α → γ) (g : β → δ) (xs : Array β) (s : State α xs.size) :
    State γ (xs.map g).size := ⟨f s.left, SliceCursor.mapState g xs s.cursor⟩

theorem next_map (f : α → γ) (g : β → δ) (xs : Array β) (s : State α xs.size) :
    (next xs s).map (fun z => (Prod.map f g z.1, mapState f g xs z.2)) =
      next (xs.map g) (mapState f g xs s) := by
  have h := SliceCursor.next_map g xs s.cursor
  simp only [next, mapState]
  rw [← h]
  simp only [Option.map_map]
  rfl

theorem output_map (f : α → γ) (g : β → δ) (xs : Array β) (s : State α xs.size) :
    (output xs s).map (Prod.map f g) = output (xs.map g) (mapState f g xs s) := by
  change ((SliceCursor.output xs s.cursor).map (fun y => (s.left, y))).map (Prod.map f g) =
    (SliceCursor.output (xs.map g) (SliceCursor.mapState g xs s.cursor)).map
      (fun y => (f s.left, y))
  rw [← SliceCursor.output_map g xs s.cursor]
  simp only [List.map_map]
  rfl

end PairCursor

namespace FilteredStream

variable {α β γ δ : Type*}

def mapCursor (f : α → γ) (g : β → δ) (xs : Array β) :
    Cursor (α := α) xs → Cursor (α := γ) (xs.map g) :=
  Option.map (PairCursor.mapState f g xs)

theorem read_map (f : α → γ) (g : β → δ) (xs : Array β) (s : Cursor (α := α) xs) :
    (read xs s).map (fun z => (Prod.map f g z.1, mapCursor f g xs z.2)) =
      read (xs.map g) (mapCursor f g xs s) := by
  cases s with
  | none => rfl
  | some s =>
    simp only [read, PaddedRows.next, mapCursor, Option.map_some]
    rw [← PairCursor.next_map f g xs s]
    simp only [Option.map_map]
    rfl

theorem view_map (f : α → γ) (g : β → δ) (xs : Array β) (s : Cursor (α := α) xs) :
    (view xs s).map (Prod.map f g) = view (xs.map g) (mapCursor f g xs s) := by
  cases s with
  | none => rfl
  | some s => exact PairCursor.output_map f g xs s

end FilteredStream

namespace PaddedRows

variable {α β : Type*}

theorem rows_map (f : α → β) (xs : Array α) (d : ℕ) (p : RowMerge.Path d) :
    (rows xs d p).map f = rows (xs.map f) d p := by
  simp only [rows, Array.size_map]
  split <;> simp only [Option.map_some, Option.map_none, Array.getElem_map]

end PaddedRows

namespace RowMerge

variable {α β σ τ : Type*} {d : ℕ}

def mapFront (f : α → β) (g : σ → τ) (x : Front d α σ) : Front d β τ :=
  ⟨x.row, f x.value, g x.after⟩

theorem front_map (f : α → β) (g : σ → τ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (p : Path d) (s : σ) :
    (front readA p s).map (mapFront f g) = front readB p (g s) := by
  unfold front
  rw [← hr]
  simp only [Option.map_map]
  rfl

theorem start_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (rows : Path d → σ) :
    Tournament.map (mapFront f g) (start (fun x => key (f x)) readA rows) =
      start key readB (fun p => g (rows p)) := by
  unfold start
  change Tournament.map (mapFront f g)
    (Tournament.build (fun x => (fun y : Front d β τ => key y.value) (mapFront f g x))
      d (fun p => front readA p (rows p))) = _
  rw [Tournament.build_map (mapFront f g) (fun y : Front d β τ => key y.value) d
    (fun p => front readA p (rows p))]
  congr 1
  funext p
  exact front_map f g readA readB hr p (rows p)

theorem advance_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (t : Tournament.Tree (Front d α σ) d) :
    (advance (fun x => key (f x)) readA t).map
      (fun z => (f z.1, Tournament.map (mapFront f g) z.2)) =
      advance key readB (Tournament.map (mapFront f g) t) := by
  simp only [advance, Tournament.winner_map]
  cases h : Tournament.winner t with
  | none => rfl
  | some x =>
    simp only [Option.map_some]
    congr 1
    apply Prod.ext
    · rfl
    change Tournament.map (mapFront f g)
      (Tournament.replace (fun y => key (mapFront f g y).value) t x.row
        (front readA x.row x.after)) =
      Tournament.replace (fun y => key y.value) (Tournament.map (mapFront f g) t)
        x.row (front readB x.row (g x.after))
    rw [Tournament.replace_map (mapFront f g) (fun y : Front d β τ => key y.value)
      t x.row (front readA x.row x.after), front_map f g readA readB hr]

theorem aligned_map (f : α → β) (g : σ → τ)
    (t : Tournament.Tree (Front d α σ) d) (h : Aligned t) :
    Aligned (Tournament.map (mapFront f g) t) := by
  intro p y hy
  rw [Tournament.lookup_map] at hy
  obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp hy
  rw [← he]
  exact h p x hx

theorem remaining_map (f : α → β) (g : σ → τ)
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (t : Tournament.Tree (Front d α σ) d) (p : Path d) :
    remaining viewB (Tournament.map (mapFront f g) t) p = (remaining viewA t p).map f := by
  unfold remaining
  rw [Tournament.lookup_map]
  cases ht : Tournament.lookup t p with
  | none => rfl
  | some x => simp only [Option.map_some, mapFront, List.map_cons, hv]

theorem rowsSorted_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (t : Tournament.Tree (Front d α σ) d) (h : RowsSorted (fun x => key (f x)) viewA t) :
    RowsSorted key viewB (Tournament.map (mapFront f g) t) := by
  intro p
  rw [remaining_map f g viewA viewB hv, List.pairwise_map]
  exact h p

theorem potential_map (f : α → β) (g : σ → τ)
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (t : Tournament.Tree (Front d α σ) d) :
    potential viewB (Tournament.map (mapFront f g) t) = potential viewA t := by
  unfold potential
  apply Finset.sum_congr rfl
  intro p _
  rw [remaining_map f g viewA viewB hv, List.length_map]

theorem trace_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (k : ℕ) (t : Tournament.Tree (Front d α σ) d) :
    (trace (fun x => key (f x)) readA k t).map f =
      trace key readB k (Tournament.map (mapFront f g) t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    have h := advance_map f g key readA readB hr t
    cases ha : advance (fun x => key (f x)) readA t with
    | none =>
      have hb : advance key readB (Tournament.map (mapFront f g) t) = none := by
        simpa only [ha, Option.map_none] using h.symm
      simp only [trace, ha, hb, List.map_nil]
    | some z =>
      obtain ⟨a, t'⟩ := z
      have hb : advance key readB (Tournament.map (mapFront f g) t) =
          some (f a, Tournament.map (mapFront f g) t') := by
        simpa only [ha, Option.map_some] using h.symm
      simp only [trace, ha, hb, List.map_cons, ih]

end RowMerge

namespace MergedReader

variable {α β σ τ : Type*} {d : ℕ}

def mapState (f : α → β) (g : σ → τ) (key : β → ℤ)
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (s : State (fun x => key (f x)) viewA d) : State key viewB d :=
  ⟨Tournament.map (RowMerge.mapFront f g) s.tree,
    Tournament.valid_map (RowMerge.mapFront f g) (fun x => key x.value) s.tree s.valid,
    RowMerge.aligned_map f g s.tree s.aligned,
    RowMerge.rowsSorted_map f g key viewA viewB hv s.tree s.sorted⟩

theorem next_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (ha : RowMerge.IsReader readA viewA) (hb : RowMerge.IsReader readB viewB)
    (s : State (fun x => key (f x)) viewA d) :
    (next (fun x => key (f x)) readA viewA ha s).map
      (fun z => (f z.1, mapState f g key viewA viewB hv z.2)) =
      next key readB viewB hb (mapState f g key viewA viewB hv s) := by
  have h := RowMerge.advance_map f g key readA readB hr s.tree
  cases he : RowMerge.advance (fun x => key (f x)) readA s.tree with
  | none =>
    have h' : RowMerge.advance key readB (Tournament.map (RowMerge.mapFront f g) s.tree) = none := by
      simpa only [he, Option.map_none] using h.symm
    rw [next_none _ _ _ _ _ he, next_none _ _ _ _ _ h']
    rfl
  | some z =>
    obtain ⟨a, t⟩ := z
    have h' : RowMerge.advance key readB (Tournament.map (RowMerge.mapFront f g) s.tree) =
        some (f a, Tournament.map (RowMerge.mapFront f g) t) := by
      simpa only [he, Option.map_some] using h.symm
    rw [next_some _ _ _ _ _ he, next_some _ _ _ _ _ h']
    rfl

theorem output_map (f : α → β) (g : σ → τ) (key : β → ℤ)
    (readA : σ → Option (α × σ)) (readB : τ → Option (β × τ))
    (hr : ∀ s, (readA s).map (fun z => (f z.1, g z.2)) = readB (g s))
    (viewA : σ → List α) (viewB : τ → List β)
    (hv : ∀ s, (viewA s).map f = viewB (g s))
    (s : State (fun x => key (f x)) viewA d) :
    (output (fun x => key (f x)) readA viewA s).map f =
      output key readB viewB (mapState f g key viewA viewB hv s) := by
  unfold output
  rw [show RowMerge.potential viewB (mapState f g key viewA viewB hv s).tree =
      RowMerge.potential viewA s.tree from RowMerge.potential_map f g viewA viewB hv s.tree]
  exact RowMerge.trace_map f g key readA readB hr _ _

end MergedReader
end LowSpaceSubsetSum

end OAI
