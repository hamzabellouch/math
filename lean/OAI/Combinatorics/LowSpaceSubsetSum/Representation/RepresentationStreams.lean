import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LeafEnumeration
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.FilteredStream

namespace OAI

/-! # Concrete sorted raw-child streams for representation -/

namespace LowSpaceSubsetSum

open scoped BigOperators

/-- Runtime fields for one low-filtered child-pair stream. -/
structure RepresentationPairData (n : ℕ) where
  weights : Fin n → ℤ
  left : RepresentationLeaf (Fin n)
  right : RepresentationLeaf (Fin n)
  lowModulus : ℤ
  modulus : ℤ
  residue : ℤ
  positive : 0 < modulus
  mode : FilteredStream.Mode
  acceptLeft : RepresentationLeaf.Occurrence (Fin n) → Bool := fun _ => true
  acceptRight : RepresentationLeaf.Occurrence (Fin n) → Bool := fun _ => true

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

abbrev Occ := RepresentationLeaf.Occurrence (Fin n)

def wl : Occ (n := n) → ℤ := RepresentationLeaf.occurrenceWeight D.weights

def leftArray : Array (Occ (n := n)) := (D.left.enumerate.filter D.acceptLeft).toArray

def rightArray : Array (Occ (n := n)) := (D.right.enumerate.filter D.acceptRight).toArray

def storedRight : Array (Occ (n := n)) :=
  ResidueSort.sort D.rightArray D.wl D.lowModulus D.modulus

abbrev State := MergedReader.State (FilteredStream.key D.wl D.wl D.modulus D.mode)
  (FilteredStream.view (α := Occ (n := n)) D.storedRight) (Nat.clog 2 D.leftArray.size)

def start : D.State :=
  FilteredStream.sortedStart D.leftArray D.rightArray D.wl D.wl D.lowModulus D.modulus
    D.residue D.positive D.mode

def read : D.State → Option (RepresentationUniverse.ChildOccurrence (Fin n) × D.State) :=
  MergedReader.next (FilteredStream.key D.wl D.wl D.modulus D.mode)
    (FilteredStream.read D.storedRight) (FilteredStream.view D.storedRight)
    (FilteredStream.reader _)

def output (s : D.State) : List (RepresentationUniverse.ChildOccurrence (Fin n)) :=
  MergedReader.output (FilteredStream.key D.wl D.wl D.modulus D.mode)
    (FilteredStream.read D.storedRight) (FilteredStream.view D.storedRight) s

theorem read_law : RowMerge.IsReader D.read D.output :=
  MergedReader.reader _ _ _ (FilteredStream.reader _)

theorem output_mem (x : RepresentationUniverse.ChildOccurrence (Fin n)) :
    x ∈ D.output D.start ↔
      (x.1 ∈ D.left.occurrences ∧ D.acceptLeft x.1 = true) ∧
        (x.2 ∈ D.right.occurrences ∧ D.acceptRight x.2 = true) ∧
        RepresentationUniverse.childWeight D.weights x % D.lowModulus = D.residue % D.lowModulus := by
  simpa only [output, start, storedRight, leftArray, rightArray, List.toList_toArray,
    List.mem_filter, RepresentationLeaf.enumerate_mem,
    wl, RepresentationUniverse.childWeight] using
    FilteredStream.sorted_output_mem D.leftArray D.rightArray D.wl D.wl D.lowModulus
      D.modulus D.residue D.positive D.mode x

theorem output_sorted : (D.output D.start).Pairwise
    (fun x y => FilteredStream.key D.wl D.wl D.modulus D.mode x ≤
      FilteredStream.key D.wl D.wl D.modulus D.mode y) :=
  FilteredStream.sorted_output_sorted D.leftArray D.rightArray D.wl D.wl D.lowModulus
    D.modulus D.residue D.positive D.mode

def lengthBound : ℕ := D.left.enumerate.length * D.right.enumerate.length

theorem output_length_le : (D.output D.start).length ≤ D.lengthBound := by
  have h := congrArg Multiset.card (FilteredStream.sorted_output_bag D.leftArray D.rightArray
    D.wl D.wl D.lowModulus D.modulus D.residue D.positive D.mode)
  simp only [Multiset.coe_card, Multiset.card_sum, List.length_map] at h
  change (D.output D.start).length = _ at h
  rw [h]
  calc
    _ ≤ ∑ _ : Fin D.leftArray.size, D.rightArray.toList.length := by
      apply Finset.sum_le_sum
      intro i _
      exact List.length_filter_le _ _
    _ ≤ D.lengthBound := by
      have hc : (Finset.univ : Finset (Fin D.leftArray.size)).card = D.leftArray.size :=
        Finset.card_fin _
      rw [Finset.sum_const, smul_eq_mul, hc]
      exact Nat.mul_le_mul (List.length_filter_le D.acceptLeft D.left.enumerate)
        (List.length_filter_le D.acceptRight D.right.enumerate)

theorem state_nodes : Tournament.nodes D.start.tree + 1 ≤ 4 * (D.leftArray.size + 1) :=
  FilteredStream.state_nodes D.leftArray D.rightArray D.wl D.wl D.lowModulus D.modulus
    D.residue D.positive D.mode

end RepresentationPairData
end LowSpaceSubsetSum

end OAI
