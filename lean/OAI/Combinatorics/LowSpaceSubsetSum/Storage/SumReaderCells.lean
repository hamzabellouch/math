import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSumReader
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.DistinctCountCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationInitializationCells

namespace OAI

/-! # Live storage of the ordinary sum tournament and distinct counter

The two arrays are immutable and shared. Tournament nodes include bounded
path representations, and the counter retains only its current tree.
The stream of Cartesian pairs is never materialized.
-/

namespace LowSpaceSubsetSum.SumReaderCells

def key (x : ℤ × ℤ) : (ℤ × ℕ) × ℕ := (MeasuredSumReader.key x, 8)

def read (ys : Array ℤ) (s : Option SumReader.Row) :
    (Option ((ℤ × ℤ) × Option SumReader.Row) × ℕ) × ℕ :=
  (MeasuredSumReader.read ys s, 16)

def width (d : ℕ) : ℕ := 10*(d+1)

def front (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    (Option (RowMerge.Front d (ℤ × ℤ) (Option SumReader.Row)) × ℕ) × ℕ :=
  let i := RepresentationInitializationCells.index d p
  if h : i.1.1 < xs.size then
    let q := read ys (some ⟨xs[i.1.1], 0⟩)
    ((q.1.1.map (fun z => ⟨p, z.1, z.2⟩), i.1.2+q.1.2+5),
      max i.2 q.2+16*(d+1)+16)
  else ((none, i.1.2+2), i.2+16)

theorem front_value (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    (front xs ys d p).1 = MeasuredSumReader.front xs ys d p := by
  simp only [front, RepresentationInitializationCells.index_value, MeasuredSumReader.front]
  split <;> rfl

theorem front_cells (xs ys : Array ℤ) (d : ℕ) (p : RowMerge.Path d) :
    (front xs ys d p).2 ≤ 64*(d+1) := by
  have h := RepresentationInitializationCells.index_cells d p
  unfold front
  dsimp only
  split <;> dsimp only [read] <;> omega

def tree (xs ys : Array ℤ) :=
  MeasuredBuildCells.run (width (Nat.clog 2 xs.size))
    (fun x => key x.value) (Nat.clog 2 xs.size) (front xs ys (Nat.clog 2 xs.size))

theorem tree_value (xs ys : Array ℤ) : (tree xs ys).1 = MeasuredSumReader.tree xs ys := by
  rw [tree, MeasuredBuildCells.run_value]
  have hf : (fun p => (front xs ys (Nat.clog 2 xs.size) p).1) =
      MeasuredSumReader.front xs ys (Nat.clog 2 xs.size) := funext (front_value xs ys _)
  rw [hf]
  rfl

def start (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (SumReader.State xs ys × ℕ) × ℕ :=
  let out := tree xs ys
  let old := MeasuredSumReader.start xs ys hs
  have he : out.1.1 = old.1.tree := congrArg Prod.fst (tree_value xs ys)
  ((⟨out.1.1, he.symm ▸ old.1.valid, he.symm ▸ old.1.aligned, he.symm ▸ old.1.sorted⟩, out.1.2),
    out.2+xs.size+ys.size+16)

theorem start_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (start xs ys hs).1 = MeasuredSumReader.start xs ys hs := by
  have ext {a b : SumReader.State xs ys} (h : a.tree = b.tree) : a = b := by
    cases a
    cases b
    cases h
    rfl
  apply Prod.ext
  · apply ext
    exact congrArg Prod.fst (tree_value xs ys)
  · change (tree xs ys).1.2 = (MeasuredSumReader.tree xs ys).2
    exact congrArg Prod.snd (tree_value xs ys)

def next (xs ys : Array ℤ) (s : SumReader.State xs ys) :=
  MeasuredReaderCells.next (width (Nat.clog 2 xs.size)) MeasuredSumReader.key
    (MeasuredSumReader.read ys) key (read ys) (fun _ => rfl) (fun _ => rfl)
    (PaddedRows.view (SumReader.view ys)) (PaddedRows.reader _ _ (SumReader.reader ys)) s

theorem next_value (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    (next xs ys s).1 = MeasuredSumReader.next xs ys s :=
  MeasuredReaderCells.next_value (width (Nat.clog 2 xs.size)) MeasuredSumReader.key
    (MeasuredSumReader.read ys) key (read ys) (fun _ => rfl) (fun _ => rfl)
    (PaddedRows.view (SumReader.view ys)) (PaddedRows.reader _ _ (SumReader.reader ys)) s

def stateCells (xs ys : Array ℤ) (s : SumReader.State xs ys) : ℕ :=
  width (Nat.clog 2 xs.size)*(Tournament.nodes s.tree+1)

theorem stateCells_eq (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    stateCells xs ys s = width (Nat.clog 2 xs.size)*2^(Nat.clog 2 xs.size+1) := by
  simp only [stateCells, Tournament.nodes_exact]

theorem next_cells (xs ys : Array ℤ) (s : SumReader.State xs ys) :
    (next xs ys s).2 ≤ (Nat.clog 2 xs.size+2)*
      (6*(width (Nat.clog 2 xs.size)*2^(Nat.clog 2 xs.size+1))+124)+8 := by
  exact MeasuredReaderCells.next_cells (width (Nat.clog 2 xs.size)) MeasuredSumReader.key
    (MeasuredSumReader.read ys) key (read ys) (fun _ => rfl) (fun _ => rfl)
    (PaddedRows.view (SumReader.view ys)) (PaddedRows.reader _ _ (SumReader.reader ys)) s 8 16
    (fun _ => le_rfl) (fun _ => le_rfl)

def count (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) : (ℕ × ℕ) × ℕ :=
  let initial := start xs ys hs
  let out := DistinctCountCells.run (stateCells xs ys) 2 (next xs ys) key
    (xs.size*ys.size) initial.1.1
  ((out.1.1, initial.1.2+out.1.2+2), initial.2+out.2+xs.size+ys.size+32)

theorem count_value (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).1 = MeasuredSumReader.count xs ys hs := by
  have hr : (fun s => (next xs ys s).1) = MeasuredSumReader.next xs ys := funext (next_value xs ys)
  simp only [count, DistinctCountCells.run_value, start_value, hr, key, MeasuredSumReader.count]

theorem count_cells_raw (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    let d := Nat.clog 2 xs.size
    let S := width d*2^(d+1)
    (count xs ys hs).2 ≤
      (d+1)*(4*S+8+64*(d+1)+64) + 2*S + (d+2)*(6*S+124)+8+42 +
        2*(xs.size+ys.size)+48 := by
  dsimp only
  have hi := MeasuredBuildCells.run_cells (width (Nat.clog 2 xs.size))
    (fun x => key x.value) 8 (64*(Nat.clog 2 xs.size+1)) (fun _ => le_rfl)
    (Nat.clog 2 xs.size) (front xs ys (Nat.clog 2 xs.size)) (front_cells xs ys _)
  have hd := DistinctCountCells.run_cells (stateCells xs ys) 2
    (width (Nat.clog 2 xs.size)*2^(Nat.clog 2 xs.size+1))
    ((Nat.clog 2 xs.size+2)*(6*(width (Nat.clog 2 xs.size)*2^(Nat.clog 2 xs.size+1))+124)+8)
    8 (next xs ys) key (fun s => le_of_eq (stateCells_eq xs ys s))
    (next_cells xs ys) (fun _ => le_rfl) (xs.size*ys.size) (start xs ys hs).1.1
  change (tree xs ys).2+xs.size+ys.size+16+_+xs.size+ys.size+32 ≤ _
  change (tree xs ys).2 ≤ _ at hi
  omega

private theorem scalar_bound (d A S q : ℕ) (hA : 1 ≤ A)
    (hS : S ≤ 40*(d+1)*A)
    (hq : q ≤ (d+1)*(4*S+8+64*(d+1)+64)+2*S+(d+2)*(6*S+124)+98+2*(A-1)) :
    q ≤ 1024*(d+2)^2*A := by
  have hdA : d+2 ≤ (d+2)*A := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (d+2) hA
  have hS' : S ≤ 40*(d+2)*A := hS.trans (Nat.mul_le_mul_right A (by omega))
  have hfirst : 4*S+8+64*(d+1)+64 ≤ 296*(d+2)*A := by nlinarith only [hS', hdA]
  have hsecond : 6*S+124 ≤ 364*(d+2)*A := by nlinarith only [hS', hdA]
  have ht := Nat.mul_le_mul (show d+1 ≤ d+2 by omega) hfirst
  have hu := Nat.mul_le_mul_left (d+2) hsecond
  have hsq : d+2 ≤ (d+2)^2 := by nlinarith
  have hsqA := Nat.mul_le_mul_right A hsq
  have hminor : 98+2*(A-1) ≤ 100*A := by omega
  nlinarith only [hq, ht, hu, hS', hsqA, hminor]

private theorem padded_pow (R : ℕ) : 2^(Nat.clog 2 R+1) ≤ 4*(R+1) := by
  have h := Tournament.padded_nodes_le R
    (Tournament.build (fun _ : Unit => (0 : ℤ)) (Nat.clog 2 R) (fun _ => none))
  simpa only [Tournament.nodes_exact] using h

private theorem normalize_count_bound (a z : ℕ) :
    a+8+42+2*z+48 = a+98+2*z := by omega

private theorem count_bound_of_raw (x y d q : ℕ) (hp : 2^(d+1) ≤ 4*(x+1))
    (h : let S := width d*2^(d+1)
      q ≤ (d+1)*(4*S+8+64*(d+1)+64)+2*S+(d+2)*(6*S+124)+8+42+2*(x+y)+48) :
    q ≤ 1024*(d+2)^2*(x+y+1) := by
  have hS : width d*2^(d+1) ≤ 40*(d+1)*(x+y+1) := by
    have h := Nat.mul_le_mul_left (10*(d+1)) hp
    unfold width
    calc
      _ ≤ 10*(d+1)*(4*(x+1)) := h
      _ ≤ 10*(d+1)*(4*(x+y+1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  dsimp only at h
  apply scalar_bound d (x+y+1) (width d*2^(d+1)) q (by omega) hS
  simpa only [Nat.add_sub_cancel, normalize_count_bound] using h

theorem count_cells (xs ys : Array ℤ) (hs : ys.toList.Pairwise (· ≤ ·)) :
    (count xs ys hs).2 ≤ 1024*(Nat.clog 2 xs.size+2)^2*(xs.size+ys.size+1) :=
  count_bound_of_raw xs.size ys.size (Nat.clog 2 xs.size) (count xs ys hs).2
    (padded_pow xs.size) (count_cells_raw xs ys hs)

end LowSpaceSubsetSum.SumReaderCells

end OAI
