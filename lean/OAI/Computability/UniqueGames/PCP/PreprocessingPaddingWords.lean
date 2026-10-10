import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.Machines.MachinePaddingRowsLemmas
import OAI.Computability.UniqueGames.PCP.PreprocessingPaddingTables

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

private theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- Split any indexed list at the actual old/new vertex boundary. -/
theorem ofFn_split {α : Type*} (h : n ≤ m) (f : Fin m → α) :
    List.ofFn f =
      List.ofFn (fun v : Fin n => f (v.castLE h)) ++
        List.ofFn (fun v : Fin (m - n) => f (PreprocessingPaddingTables.vertexEquiv h (.inr v))) := by
  calc
    List.ofFn f = List.ofFn
        (fun v : Fin (n + (m - n)) => f (Fin.cast (Nat.add_sub_of_le h) v)) :=
      List.ofFn_congr (Nat.add_sub_of_le h).symm f
    _ = _ := by rw [List.ofFn_add]; rfl

/-- Mixed-radix row order is vertex-major, then increasing port order. -/
theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

/-- The bits of one actual table row, in the existing graph codec. -/
def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

/-- The old encoded rows, without their two header words. -/
def rowsBits (table : Table n d) : List Bool :=
  encodeWords ((flatRows table).toList.flatMap GraphTables.rowWords)

/-- Recover the original flat row from its exact mixed-radix coordinates. -/
theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

/-- Serializing all rows agrees with grouping their bits by vertex and port. -/
theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

/-- Every bit in an original row survives padding unchanged. -/
theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

/-- A new row is the machine's self-loop row with its actual global index. -/
theorem rowBits_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) p =
      MachineDummyRows.rowBits (n + v.val) (p.val + d * (n + v.val)) := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_new,
    PreprocessingPaddingTables.relations_pad_new]
  rfl

/-- The row emitter's recursive stream enumerates successive reverse indices. -/
theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

/-- The vertex emitter's recursive stream enumerates consecutive vertex blocks. -/
theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

/-- The new vertex's complete port block equals the actual machine block. -/
theorem vertexBits_pad_new (table : Table n d) (h : n ≤ m) (v : Fin (m - n)) :
    vertexBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) =
      MachineDummyRows.rowsBits (n + v.val) (n * d + v.val * d) d := by
  unfold vertexBits
  simp_rw [rowBits_pad_new]
  rw [dummy_rowsBits_eq_ofFn]
  apply congrArg (fun f : Fin d → List Bool => (List.ofFn f).flatten)
  funext p
  congr 1
  ring

/-- The actual padded row codec is the old row codec followed by the emitted suffix. -/
theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

/-- Exact final codec identity used by the machine-output correspondence. -/
theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
