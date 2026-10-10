import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredInitialization

namespace OAI

/-! # Initialization retaining explicit shared arrays

The row closure captures the shared right array. Row and reader callbacks
reuse this array without rebuilding it.
-/

namespace LowSpaceSubsetSum.RepresentationArrayInitialization

variable {n : ℕ}

private theorem key_apply (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (x : LeafRecord n × LeafRecord n) :
    (RepresentationKeys.pairKey I F P mode x).1 =
      FilteredStream.key (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) P mode x := by
  cases mode <;> rfl

def tree (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (mode : FilteredStream.Mode) :=
  FilteredStream.measuredInitialTree left right (RepresentationKeys.pairKey I F P mode)
    (RepresentationKeys.row I F right p P c hs mode) (Nat.clog 2 left.size)

theorem tree_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (tree I F left right p P c hs mode).1 =
      (FilteredStream.start left right (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) p P c hs ht hP mode).tree := by
  simp only [tree, FilteredStream.measuredInitialTree_value, RepresentationKeys.row_value,
    key_apply, FilteredStream.start, MergedReader.start, FilteredStream.rowArray]

def start (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    MergedReader.State
      (FilteredStream.key (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) P mode)
      (FilteredStream.view right) (Nat.clog 2 left.size) × ℕ :=
  let out := tree I F left right p P c hs mode
  let source := FilteredStream.start left right (fun x => (RepresentationKeys.leafWeight I F x).1)
    (fun x => (RepresentationKeys.leafWeight I F x).1) p P c hs ht hP mode
  have he : out.1 = source.tree := tree_value I F left right p P c hs ht hP mode
  (⟨out.1, he.symm ▸ source.valid, he.symm ▸ source.aligned, he.symm ▸ source.sorted⟩, out.2)

theorem start_value (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (start I F left right p P c hs ht hP mode).1 =
      FilteredStream.start left right (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) p P c hs ht hP mode := by
  have ext {key : (LeafRecord n × LeafRecord n) → ℤ}
      {a b : MergedReader.State key (FilteredStream.view right) (Nat.clog 2 left.size)}
      (h : a.tree = b.tree) : a = b := by
    cases a
    cases b
    cases h
    rfl
  apply ext
  exact tree_value I F left right p P c hs ht hP mode

theorem start_work (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) (hn : 10000 ≤ n)
    (hL : left.size ≤ 2 ^ n) (hR : right.size ≤ 2 ^ n) :
    (start I F left right p P c hs ht hP mode).2 ≤ inputScale I ^ 8 * (left.size + 1) := by
  have hw := FilteredStream.measuredInitialTree_work left right
    (RepresentationKeys.pairKey I F P mode) (RepresentationKeys.row I F right p P c hs mode)
    (inputScale I ^ 3) (inputScale I ^ 5)
    (fun x => RepresentationKeys.pairKey_scale I F P mode x hn)
    (fun x => RepresentationKeys.row_scale I F right p P c hs mode x hn hR)
    (Nat.clog 2 left.size)
  have hd := Nat.clog_le_of_le_pow hL
  have hsquare := Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
  have hp := Tournament.padded_nodes_le left.size (tree I F left right p P c hs mode).1
  rw [Tournament.nodes_exact, pow_succ] at hp
  have hpad : 2 ^ Nat.clog 2 left.size ≤ 2 * (left.size + 1) := by omega
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu1 : 1 ≤ inputScale I := by omega
  have h25 : inputScale I ^ 2 ≤ inputScale I ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have h35 : inputScale I ^ 3 ≤ inputScale I ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have hn2 := Nat.pow_le_pow_left hnu 2
  have hc : 39 ≤ 39 * inputScale I ^ 5 := Nat.le_mul_of_pos_right _ (by positivity)
  have hscale : 92 * inputScale I ^ 5 ≤ inputScale I ^ 8 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = inputScale I ^ 6 := (pow_succ' _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hu1 (by decide)
  have hpoly : 2 * (4 * (n + 1) ^ 2 + inputScale I ^ 5 + 2 * inputScale I ^ 3 + 39) ≤
      inputScale I ^ 8 := by omega
  change (tree I F left right p P c hs mode).2 ≤ _
  calc
    _ ≤ (4 * (Nat.clog 2 left.size + 1) ^ 2 + inputScale I ^ 5 +
        2 * inputScale I ^ 3 + 39) * 2 ^ Nat.clog 2 left.size := hw
    _ ≤ (4 * (n + 1) ^ 2 + inputScale I ^ 5 + 2 * inputScale I ^ 3 + 39) *
        (2 * (left.size + 1)) := Nat.mul_le_mul (by omega) hpad
    _ = (2 * (4 * (n + 1) ^ 2 + inputScale I ^ 5 + 2 * inputScale I ^ 3 + 39)) *
        (left.size + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hpoly

end LowSpaceSubsetSum.RepresentationArrayInitialization

end OAI
