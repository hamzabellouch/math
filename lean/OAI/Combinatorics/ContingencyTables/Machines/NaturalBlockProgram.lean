import OAI.Combinatorics.ContingencyTables.Machines.DependentWordProgram
import Mathlib.Data.List.SplitLengths

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Input := List ℕ × List ℕ
abbrev Entry := Input × ℕ

def start (z : Entry) : ℕ := (z.1.1.take z.2).sum
def startRealizer : Realizer start :=
  composition (composition (pair (composition first first) second) takeFast) listSum
lemma polynomial_start : PolynomialTime startRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_takeFast) polynomial_listSum

def block (z : Entry) : List ℕ :=
  (z.1.2.drop (start z)).take (z.1.1.getD z.2 0)
def blockRealizer : Realizer block :=
  composition (pair
    (composition (pair (composition first second) startRealizer) dropFast)
    (composition (pair (composition first first) second) (getDFast 0))) takeFast
lemma polynomial_block : PolynomialTime blockRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_start)
      polynomial_dropFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))) polynomial_takeFast

def indices (z : Input) : List ℕ := List.range z.1.length
def indicesRealizer : Realizer indices := composition (composition first listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def blocks (z : Input) : List (List ℕ) := (indices z).map (fun i => block (z,i))
def blocksRealizer : Realizer blocks :=
  composition (pair identity indicesRealizer) (mapWith blockRealizer)
theorem polynomial_blocks : PolynomialTime blocksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_block)

lemma block_splitLengths (widths values : List ℕ) (i : ℕ) :
    block ((widths,values),i)=(widths.splitLengths values).getD i [] := by
  induction widths generalizing values i with
  | nil => simp [block,start]
  | cons w ws ih =>
    cases i with
    | zero => simp [block,start,List.splitLengths_cons]
    | succ i =>
      simpa only [block,start,List.take_succ_cons,List.sum_cons,List.getD_cons_succ,
        List.splitLengths_cons,List.drop_drop,Nat.add_comm] using ih (values.drop w) i

theorem blocks_eq_splitLengths (widths values : List ℕ) :
    blocks (widths,values)=widths.splitLengths values := by
  apply List.ext_getElem
  · simp [blocks,indices]
  · intro i hi hj
    have hiw : i < widths.length := by
      simpa only [blocks,indices,List.length_map,List.length_range] using hi
    simp only [blocks,indices,List.getElem_map,List.getElem_range]
    have h := block_splitLengths widths values i
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using h

lemma splitLengths_flatten (rows : List (List ℕ)) :
    (rows.map List.length).splitLengths rows.flatten=rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simpa only [List.map_cons,List.flatten_cons,List.splitLengths_cons,
      List.take_left,List.drop_left] using congrArg (List.cons row) ih

/-- A literal list of rows is recovered exactly from its stored row
lengths and its flattened code, including rows of length zero. -/
theorem blocks_flatten (rows : List (List ℕ)) :
    blocks (rows.map List.length,rows.flatten)=rows := by
  rw [blocks_eq_splitLengths,splitLengths_flatten]

end ContingencyTables.NaturalBlockProgram

end OAI
