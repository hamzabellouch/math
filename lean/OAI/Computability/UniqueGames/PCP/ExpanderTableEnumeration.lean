import Mathlib.Data.List.OfFn
import OAI.Computability.UniqueGames.PCP.ExpanderRowControlLemmas

namespace OAI

section

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity

variable {v d : Nat}

/-- Input position in the actual next table, with port varying fastest. -/
def globalIndex (vertex : Fin v) (position : Fin (rowFactor d)) :
    Fin ((v * cloudSize d) * degree d) :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  rowIndex (v * cloudSize d) (degree d)
    (rowIndex v (cloudSize d) (vertex, pair.1), pair.2)

theorem globalIndex_val (vertex : Fin v) (position : Fin (rowFactor d)) :
    (globalIndex vertex position).val = position.val + rowFactor d * vertex.val := by
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  have hp := congrArg Fin.val
    ((rowIndex (cloudSize d) (degree d)).apply_symm_apply position)
  change pair.2.val + degree d * pair.1.val = position.val at hp
  change pair.2.val + degree d * (pair.1.val + cloudSize d * vertex.val) = _
  calc
    _ = (pair.2.val + degree d * pair.1.val) + rowFactor d * vertex.val := by
      dsimp only [rowFactor]
      ring
    _ = position.val + rowFactor d * vertex.val := by rw [hp]

/-- The number emitted by the checked pure row evaluator. -/
def rowValue (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) : Nat :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  let result := evaluateRow G H vertex pair.1 pair.2
  outputAddress result.1.val result.2

theorem rowValue_eq_reverseIndex (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    rowValue G H vertex position = (reverseIndex (step G H) (globalIndex vertex position)).val := by
  exact outputAddress_eq_step_reverseIndex G H vertex
    ((rowIndex (cloudSize d) (degree d)).symm position).1
    ((rowIndex (cloudSize d) (degree d)).symm position).2

def vertexWords (G : Table v (degree d)) (H : Table (cloudSize d) d) (vertex : Fin v) :
    List Nat := List.ofFn (rowValue G H vertex)

def generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d) : List Nat :=
  (List.ofFn (vertexWords G H)).flatten

@[simp] theorem vertexWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).length = rowFactor d := by
  simp [vertexWords]

theorem vertexWords_drop_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    (vertexWords G H vertex).drop position.val =
      rowValue G H vertex position :: (vertexWords G H vertex).drop (position.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [vertexWords]

@[simp] theorem vertexWords_drop_full (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).drop (rowFactor d) = [] := by
  apply List.drop_eq_nil_of_le
  simp

theorem vertexWords_drop_last (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d))
    (last : position.val + 1 = rowFactor d) :
    (vertexWords G H vertex).drop position.val = [rowValue G H vertex position] := by
  rw [vertexWords_drop_succ, last, vertexWords_drop_full]

private theorem ofFn_cast {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

theorem rotationWords_eq_ofFn {n q : Nat} (G : Table n q) :
    rotationWords G = List.ofFn (fun i : Fin (n * q) => (reverseIndex G i).val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn]
    exact rotationWords_getElem G i (by simpa only [rotationWords_length] using hi)

/-- Associativity of the three stored mixed-radix coordinates. -/
theorem rowCount_eq : v * rowFactor d = (v * cloudSize d) * degree d :=
  (Nat.mul_assoc v (cloudSize d) (degree d)).symm

theorem generatedWords_eq_flat_ofFn (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = List.ofFn (fun i : Fin (v * rowFactor d) =>
      (reverseIndex (step G H) (Fin.cast rowCount_eq i)).val) := by
  rw [List.ofFn_mul]
  unfold generatedWords vertexWords
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext vertex
  apply congrArg List.ofFn
  funext position
  rw [rowValue_eq_reverseIndex]
  apply congrArg (fun i : Fin ((v * cloudSize d) * degree d) =>
    (reverseIndex (step G H) i).val)
  apply Fin.ext
  rw [globalIndex_val]
  change position.val + rowFactor d * vertex.val = vertex.val * rowFactor d + position.val
  ac_rfl

/-- Complete equality with the actual materialized next-table word order. -/
theorem generatedWords_eq_rotationWords (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = rotationWords (step G H) := by
  rw [generatedWords_eq_flat_ofFn]
  exact (ofFn_cast (rowCount_eq (v := v) (d := d))
    (fun i => (reverseIndex (step G H) i).val)).trans
    (rotationWords_eq_ofFn (step G H)).symm

@[simp] theorem generatedWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (generatedWords G H).length = v * rowFactor d := by
  rw [generatedWords_eq_rotationWords, rotationWords_length]
  exact rowCount_eq.symm

def priorVertices (G : Table v (degree d)) (H : Table (cloudSize d) d) (count : Nat) :
    List Nat := ((List.ofFn (vertexWords G H)).take count).flatten

def prefixRows (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (completedPositions : Nat) : List Nat :=
  priorVertices G H vertex.val ++ (vertexWords G H vertex).take completedPositions

@[simp] theorem priorVertices_zero (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H 0 = [] := by simp [priorVertices]

@[simp] theorem priorVertices_full (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H v = generatedWords G H := by
  unfold priorVertices generatedWords
  rw [List.take_of_length_le (by simp)]

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

@[simp] theorem prefixRows_zero (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : prefixRows G H vertex 0 = priorVertices G H vertex.val := by
  simp [prefixRows]

theorem prefixRows_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (r : Nat) (hr : r < rowFactor d) :
    prefixRows G H vertex (r + 1) =
      prefixRows G H vertex r ++ [rowValue G H vertex ⟨r, hr⟩] := by
  unfold prefixRows
  rw [List.take_succ_eq_append_getElem (by simpa using hr)]
  simp [vertexWords, List.append_assoc]

theorem prefixRows_complete (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) :
    prefixRows G H vertex (rowFactor d) = priorVertices G H (vertex.val + 1) := by
  rw [prefixRows, List.take_of_length_le (by simp)]
  simpa using (priorVertices_succ G H vertex.val vertex.isLt).symm

/-- This is exactly the accumulator update performed after each emitted row. -/
def accumulate (values : List Nat) (initial : List Bool) : List Bool :=
  values.foldl (fun accumulator value => (encodeWord value).reverse ++ accumulator) initial

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_prefixRows_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (r : Nat) (hr : r < rowFactor d) (initial : List Bool) :
    accumulate (prefixRows G H vertex (r + 1)) initial =
      (encodeWord (rowValue G H vertex ⟨r, hr⟩)).reverse ++
        accumulate (prefixRows G H vertex r) initial := by
  rw [prefixRows_succ G H vertex r hr, accumulate_append]
  rfl

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

theorem accumulate_generatedWords_length_le (G : Table v (degree d))
    (H : Table (cloudSize d) d) (initial : List Bool) :
    (accumulate (generatedWords G H) initial).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) + initial.length := by
  rw [accumulate_eq, List.length_append, List.length_reverse]
  exact Nat.add_le_add_right (encode_generatedWords_length_le G H) initial.length

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
