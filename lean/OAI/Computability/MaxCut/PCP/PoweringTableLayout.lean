import Mathlib
import OAI.Computability.MaxCut.PCP.PoweringOpinionTables

namespace OAI

/-!
# Vertex-major serialization of the actual powering table

Each vertex contributes a fixed number of consecutive stored dart rows. The
identities below group the actual vector, including every predicate entry, and
then apply the shared word codec. They do not assume an output layout or assert
a machine running time. Unary bit lengths can vary with the stored indices.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTableLayout

open MaxCutGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

/-- One adjacent orientation pair for each recorded port word. -/
def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  unfold dartCount
  simp only [blockSize]
  ac_rfl

/-- The index of a stored row within the consecutive block of vertex `v`. -/
def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

/-- The consecutive block is the actual vertex-major recorded-walk order. -/
theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  erw [blockIndex_val]

/-- Exactly the stored rows at positions `B*v, ..., B*v+B-1`. -/
def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

/-- All fields of these stored rows, in their actual codec order. -/
def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

/-- Actual unary serialization of the complete vertex block. -/
def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)

@[simp] theorem vertexRows_length {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (v : Fin vertices) :
    (vertexRows input n v).length = blockSize d n := by
  simp only [vertexRows]
  exact List.length_ofFn

private theorem vector_toList_ofFn_inline_PoweringTableLayout {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

/-- Regroup a stored vector without changing, omitting, or permuting a row. -/
private theorem vector_blocks_inline_PoweringTableLayout {α : Type*} {m vertices width : Nat}
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
  rw [vector_toList_ofFn_inline_PoweringTableLayout rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

/-- Every actual stored row occurs once in its vertex's consecutive block. -/
theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks_inline_PoweringTableLayout (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

/-- The full word stream, including its two header fields, in vertex order. -/
theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  erw [List.flatMap_assoc]
  rfl

private theorem encodeWords_flatMap_inline_PoweringTableLayout {α : Type*} (items : List α)
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
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap_inline_PoweringTableLayout]
  rfl

/-- Each stored row has its tail, reversal, and every ordered predicate bit. -/
theorem vertexRowWords_length {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowWords input n v).length =
      (labelCount d n * labelCount d n + 2) * blockSize d n := by
  unfold vertexRowWords
  rw [GenericGraphTables.rowsWords_length, vertexRows_length]

/-- Every natural field contributes at least its unary delimiter. -/
theorem vertexRowBits_length_ge {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (labelCount d n * labelCount d n + 2) * blockSize d n ≤
      (vertexRowBits input n v).length := by
  unfold vertexRowBits
  rw [encodeWords_length, vertexRowWords_length]
  omega

/-- Actual unary row blocks have a uniform bound from the two index bounds. -/
theorem vertexRowBits_length_le {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowBits input n v).length ≤
      blockSize d n *
        (vertices + dartCount vertices d n + 2 * (labelCount d n * labelCount d n)) := by
  have h := GenericGraphTables.rowsBits_length_le (vertexRows input n v)
  rw [vertexRows_length] at h
  exact h

/-- The actual unary header contains the two declared counts. -/
theorem outputHeader_length (vertices d n : Nat) :
    (encodeWords [vertices, dartCount vertices d n]).length =
      vertices + dartCount vertices d n + 2 := by
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end MaxCutGames.Foundations.PCP.PoweringTableLayout

end OAI
