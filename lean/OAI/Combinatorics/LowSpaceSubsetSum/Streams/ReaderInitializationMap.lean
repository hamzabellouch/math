import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ReaderMap

namespace OAI

/-! # Semantic maps commute with the actual binary-search initialization -/

namespace LowSpaceSubsetSum
namespace BinarySlice

variable {α β : Type*}

private theorem search_lo_congr {m n : ℕ} (h : m = n)
    (p : Fin m → Bool) (q : Fin n → Bool)
    (hpq : ∀ i j, i.val = j.val → p i = q j) (k : ℕ) :
    (BinaryPivot.search p k).lo = (BinaryPivot.search q k).lo := by
  subst n
  have he : p = q := funext (fun i => hpq i i rfl)
  rw [he]

theorem lower_map (f : α → β) (xs : Array α) (key : β → ℤ) (r : ℤ) (k : ℕ) :
    lower (xs.map f) key r k = lower xs (fun x => key (f x)) r k := by
  unfold lower
  apply search_lo_congr Array.size_map
  intro i j hij
  simp only [Array.getElem_map, hij]

theorem upper_map (f : α → β) (xs : Array α) (key : β → ℤ) (r : ℤ) (k : ℕ) :
    upper (xs.map f) key r k = upper xs (fun x => key (f x)) r k := by
  unfold upper
  apply search_lo_congr Array.size_map
  intro i j hij
  simp only [Array.getElem_map, hij]

theorem range_map (f : α → β) (xs : Array α) (key : β → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key (f xs[i.val])))
    (ht : Monotone (fun i : Fin (xs.map f).size => key (xs.map f)[i.val]))
    (hk : xs.size < 2 ^ k) (hk' : (xs.map f).size < 2 ^ k) :
    SliceCursor.mapRange f xs (range xs (fun x => key (f x)) r k hs hk) =
      range (xs.map f) key r k ht hk' := by
  simp only [SliceCursor.mapRange, range, lower_map, upper_map]

end BinarySlice
namespace SliceModular

variable {α β : Type*}

theorem forward_map (f : α → β) (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : β → ℤ) (P r : ℤ) (k : ℕ) :
    SliceCursor.mapState f xs (forward xs rr (fun x => key (f x)) P r k) =
      forward (xs.map f) (SliceCursor.mapRange f xs rr) key P r k := by
  by_cases h : 0 < rr.length
  · have : NeZero rr.length := ⟨by omega⟩
    rw [forward, dite_eq_left h, forward, dite_eq_left (show 0 < (SliceCursor.mapRange f xs rr).length from h)]
    simp only [SliceCursor.mapState, SliceCursor.mapRange,
      ModularCursor.forwardStart, SliceCursor.values, Array.getElem_map]
    rfl
  · rw [forward, dite_eq_right h, forward, dite_eq_right (show ¬ 0 < (SliceCursor.mapRange f xs rr).length from h)]
    rfl

theorem reverse_map (f : α → β) (xs : Array α) (rr : SliceCursor.Range xs.size)
    (key : β → ℤ) (r : ℤ) (k : ℕ) :
    SliceCursor.mapState f xs (reverse xs rr (fun x => key (f x)) r k) =
      reverse (xs.map f) (SliceCursor.mapRange f xs rr) key r k := by
  by_cases h : 0 < rr.length
  · have : NeZero rr.length := ⟨by omega⟩
    rw [reverse, dite_eq_left h, reverse, dite_eq_left (show 0 < (SliceCursor.mapRange f xs rr).length from h)]
    simp only [SliceCursor.mapState, SliceCursor.mapRange,
      ModularCursor.reverseStart, SliceCursor.values, Array.getElem_map]
    rfl
  · rw [reverse, dite_eq_right h, reverse, dite_eq_right (show ¬ 0 < (SliceCursor.mapRange f xs rr).length from h)]
    rfl

end SliceModular
namespace FilteredRow

variable {α β γ δ : Type*}

theorem forward_map (f : α → γ) (g : β → δ) (xs : Array β)
    (wl : γ → ℤ) (wr : δ → ℤ) (p P c : ℤ) (k : ℕ)
    (hs : PrimarySorted xs (fun y => wr (g y)) p)
    (ht : PrimarySorted (xs.map g) wr p)
    (hk : xs.size < 2 ^ k) (hk' : (xs.map g).size < 2 ^ k) (x : α) :
    PairCursor.mapState f g xs
      (forward xs (fun y => wl (f y)) (fun y => wr (g y)) p P c k hs hk x) =
      forward (xs.map g) wl wr p P c k ht hk' (f x) := by
  simp only [forward, PairCursor.mapState, range]
  congr 1
  rw [SliceModular.forward_map g xs _ (fun y => wr y % P) P (wl (f x) % P) k]
  congr 1
  exact BinarySlice.range_map g xs (fun y => wr y % p) _ k hs ht hk hk'

theorem reverse_map (f : α → γ) (g : β → δ) (xs : Array β)
    (wl : γ → ℤ) (wr : δ → ℤ) (p P c v : ℤ) (k : ℕ)
    (hs : PrimarySorted xs (fun y => wr (g y)) p)
    (ht : PrimarySorted (xs.map g) wr p)
    (hk : xs.size < 2 ^ k) (hk' : (xs.map g).size < 2 ^ k) (x : α) :
    PairCursor.mapState f g xs
      (reverse xs (fun y => wl (f y)) (fun y => wr (g y)) p P c v k hs hk x) =
      reverse (xs.map g) wl wr p P c v k ht hk' (f x) := by
  simp only [reverse, PairCursor.mapState, range]
  congr 1
  rw [SliceModular.reverse_map g xs _ (fun y => wr y % P) ((v - wl (f x)) % P) k]
  congr 1
  exact BinarySlice.range_map g xs (fun y => wr y % p) _ k hs ht hk hk'

end FilteredRow
namespace FilteredStream

variable {α β γ δ : Type*}

theorem key_map (f : α → γ) (g : β → δ) (wl : γ → ℤ) (wr : δ → ℤ)
    (P : ℤ) (mode : Mode) (x : α × β) :
    key (fun y => wl (f y)) (fun y => wr (g y)) P mode x =
      key wl wr P mode (Prod.map f g x) := by
  cases mode <;> rfl

theorem row_map (f : α → γ) (g : β → δ) (right : Array β)
    (wl : γ → ℤ) (wr : δ → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun y => wr (g y)) p)
    (ht : FilteredRow.PrimarySorted (right.map g) wr p) (mode : Mode) (x : α) :
    PairCursor.mapState f g right
      (row right (fun y => wl (f y)) (fun y => wr (g y)) p P c hs mode x) =
      row (right.map g) wl wr p P c ht mode (f x) := by
  cases mode with
  | direct =>
    simpa only [row, Array.size_map] using
      FilteredRow.forward_map f g right wl wr p P c (steps right.size) hs ht
        (steps_sufficient right.size) (by simpa using steps_sufficient right.size) x
  | complementary v =>
    simpa only [row, Array.size_map] using
      FilteredRow.reverse_map f g right wl wr p P c v (steps right.size) hs ht
        (steps_sufficient right.size) (by simpa using steps_sufficient right.size) x

theorem rowArray_map (f : α → γ) (g : β → δ) (left : Array α) (right : Array β)
    (wl : γ → ℤ) (wr : δ → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun y => wr (g y)) p)
    (ht : FilteredRow.PrimarySorted (right.map g) wr p) (mode : Mode) :
    (rowArray left right (fun y => wl (f y)) (fun y => wr (g y)) p P c hs mode).map
      (PairCursor.mapState f g right) =
      rowArray (left.map f) (right.map g) wl wr p P c ht mode := by
  apply Array.toList_inj.mp
  simp only [rowArray, Array.toList_map, List.map_map]
  congr 1
  funext x
  exact row_map f g right wl wr p P c hs ht mode x

theorem initial_tree_map (f : α → γ) (g : β → δ) (left : Array α) (right : Array β)
    (wl : γ → ℤ) (wr : δ → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun y => wr (g y)) p)
    (ht : FilteredRow.PrimarySorted (right.map g) wr p) (mode : Mode) (d : ℕ) :
    Tournament.map (RowMerge.mapFront (Prod.map f g) (mapCursor f g right))
      (RowMerge.start (key (fun y => wl (f y)) (fun y => wr (g y)) P mode)
        (read right)
        (PaddedRows.rows (rowArray left right (fun y => wl (f y))
          (fun y => wr (g y)) p P c hs mode) d)) =
      RowMerge.start (key wl wr P mode) (read (right.map g))
        (PaddedRows.rows (rowArray (left.map f) (right.map g) wl wr p P c ht mode) d) := by
  have he : key (fun y => wl (f y)) (fun y => wr (g y)) P mode =
      (fun x => key wl wr P mode (Prod.map f g x)) := by cases mode <;> rfl
  rw [he, RowMerge.start_map (Prod.map f g) (mapCursor f g right)
    (key wl wr P mode) (read right) (read (right.map g)) (read_map f g right)]
  congr 1
  funext path
  change (PaddedRows.rows _ d path).map (PairCursor.mapState f g right) = _
  rw [PaddedRows.rows_map, rowArray_map f g left right wl wr p P c hs ht mode]

end FilteredStream

end LowSpaceSubsetSum

end OAI
