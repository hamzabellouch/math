import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTableLayout

open IndependentSetsGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  unfold dartCount blockSize
  ac_rfl

def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  change (dartBlockEquiv d n (p, direction)).val + blockSize d n * v.val =
    (dartEquiv vertices d n (direction, (v, p))).val
  rw [dartEquiv_val, dartBlockEquiv_val]
  unfold blockSize
  omega

def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)

@[simp] theorem vertexRows_length {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (v : Fin vertices) :
    (vertexRows input n v).length = blockSize d n := by
  exact List.length_ofFn

private theorem vector_toList_ofFn {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

private theorem vector_blocks {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  have atIndex (v : Fin vertices) (j : Fin width)
      (h : v.val * width + j.val < vertices * width) :
      (⟨v.val * width + j.val, h⟩ : Fin (vertices * width)) =
        finProdFinEquiv (v, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [vector_toList_ofFn rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  exact congrArg ([vertices, dartCount vertices d n] ++ ·) List.flatMap_assoc

theorem encodeWords_flatMap {α : Type*} (items : List α)
    (words : α → List Nat) :
    encodeWords (items.flatMap words) =
      items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap]
  rfl

theorem vertexRowWords_length {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowWords input n v).length =
      (labelCount d n * labelCount d n + 2) * blockSize d n := by
  unfold vertexRowWords
  rw [GenericGraphTables.rowsWords_length, vertexRows_length]

theorem vertexRowBits_length_ge {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (labelCount d n * labelCount d n + 2) * blockSize d n ≤
      (vertexRowBits input n v).length := by
  unfold vertexRowBits
  rw [encodeWords_length, vertexRowWords_length]
  omega

theorem vertexRowBits_length_le {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowBits input n v).length ≤
      blockSize d n *
        (vertices + dartCount vertices d n + 2 * (labelCount d n * labelCount d n)) := by
  have h := GenericGraphTables.rowsBits_length_le (vertexRows input n v)
  rw [vertexRows_length] at h
  exact h

theorem outputHeader_length (vertices d n : Nat) :
    (encodeWords [vertices, dartCount vertices d n]).length =
      vertices + dartCount vertices d n + 2 := by
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end IndependentSetsGames.Foundations.PCP.PoweringTableLayout

end OAI
