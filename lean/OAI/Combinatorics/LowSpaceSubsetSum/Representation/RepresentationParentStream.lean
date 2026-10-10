import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStreams
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RecordedJoin
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MaskRestriction
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.WeightEncoding

namespace OAI

/-! # Executable bounded parent tasks with early leaf restrictions -/

namespace LowSpaceSubsetSum

instance {n : ℕ} (x : RepresentationUniverse.ParentOccurrence (Fin n)) :
    Decidable (RepresentationUniverse.Valid x) := by
  unfold RepresentationUniverse.Valid RepresentationUniverse.DisjointFour
  infer_instance

/-- Data available to a parent task: input, signs, leaf domains, moduli,
residues, capacity, and the current partial top mask. No solution is stored. -/
structure RepresentationParentData (n : ℕ) where
  input : Instance n
  signs : Finset (Fin n)
  leaves : Fin 4 → RepresentationLeaf (Fin n)
  lowModulus : ℤ
  modulus : ℤ
  positive : 0 < modulus
  childResidues : Fin 2 → ℤ
  parentResidue : ℤ
  capacity : ℕ
  maskRestriction : MaskRestriction n

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

def weights : Fin n → ℤ := flip (fun i => (D.input.values i : ℤ)) D.signs

def pair (j : Fin 2) : RepresentationPairData n where
  weights := D.weights
  left := D.leaves ⟨2 * j.val, by omega⟩
  right := D.leaves ⟨2 * j.val + 1, by omega⟩
  lowModulus := D.lowModulus
  modulus := D.modulus
  residue := D.childResidues j
  positive := D.positive
  mode := if j = 0 then .direct else .complementary D.parentResidue
  acceptLeft x := D.maskRestriction.accept (D.leaves ⟨2 * j.val, by omega⟩).top x.1.1
  acceptRight x := D.maskRestriction.accept (D.leaves ⟨2 * j.val + 1, by omega⟩).top x.1.1

abbrev Child := RepresentationUniverse.ChildOccurrence (Fin n)
abbrev Parent := RepresentationUniverse.ParentOccurrence (Fin n)

def key (j : Fin 2) : Child (n := n) → ℤ :=
  FilteredStream.key (D.pair j).wl (D.pair j).wl D.modulus (D.pair j).mode

/-- All top and background validity checks are redundant on the intended
layout, but keep the subset-witness invariant explicit on arbitrary data. -/
def emit (x y : Child (n := n)) : Option (Entry (Fin n)) :=
  if RepresentationUniverse.Valid (x, y)
  then some (RepresentationUniverse.entry D.weights (x, y)) else none

theorem emit_some_iff (x y : Child (n := n)) (e : Entry (Fin n)) :
    D.emit x y = some e ↔ RepresentationUniverse.Valid (x, y) ∧
      RepresentationUniverse.entry D.weights (x, y) = e := by
  simp only [emit]
  split_ifs <;> simp_all

def collect (B : ℕ) :=
  StreamJoin.stopped (D.pair 0).read (D.key 0) (D.pair 1).read (D.key 1)
    (RecordedDictionary.callback D.capacity (WeightEncoding.entryKey D.input) D.emit)
    B (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (D.pair 0).start (D.pair 1).start RecordedDictionary.empty

def entries (B : ℕ) : Array (Entry (Fin n)) := (D.collect B).state.user.records

theorem collect_invariant (B : ℕ) :
    RecordedDictionary.Invariant D.capacity (WeightEncoding.entryWidth D.input)
      (WeightEncoding.entryKey D.input) (D.collect B).state.user := by
  exact RecordedDictionary.stopped_invariant _ _ _ _ _
    (WeightEncoding.entryKey_length D.input) _ _ _ _ _ _ _

/-- All outcomes, including overflow, retain at most one rejected entry. -/
theorem storage (B : ℕ) :
    (D.entries B).size ≤ D.capacity + 1 ∧
      BinaryTrie.nodes (D.collect B).state.user.keys.tree ≤
        (WeightEncoding.entryWidth D.input + 1) * (D.capacity + 1) :=
  RecordedDictionary.storage (D.collect_invariant B)

theorem streams_parent (x y : Child (n := n))
    (hx : x ∈ (D.pair 0).output (D.pair 0).start)
    (hy : y ∈ (D.pair 1).output (D.pair 1).start) :
    (x, y) ∈ RepresentationUniverse.parents D.leaves := by
  have hx := ((D.pair 0).output_mem x).mp hx
  have hy := ((D.pair 1).output_mem y).mp hy
  exact (RepresentationUniverse.mem_parents D.leaves (x, y)).mpr
    ⟨hx.1.1, hx.2.1.1, hy.1.1, hy.2.1.1⟩

theorem streams_compatible (x y : Child (n := n))
    (hx : x ∈ (D.pair 0).output (D.pair 0).start)
    (hy : y ∈ (D.pair 1).output (D.pair 1).start) :
    D.maskRestriction.Compatible (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.topMask (x, y)) := by
  have hx := ((D.pair 0).output_mem x).mp hx
  have hy := ((D.pair 1).output_mem y).mp hy
  have h0 := (D.maskRestriction.accept_eq_true _ _).mp hx.1.2
  have h1 := (D.maskRestriction.accept_eq_true _ _).mp hx.2.1.2
  have h2 := (D.maskRestriction.accept_eq_true _ _).mp hy.1.2
  have h3 := (D.maskRestriction.accept_eq_true _ _).mp hy.2.1.2
  exact D.maskRestriction.union_compatible (D.maskRestriction.union_compatible (D.maskRestriction.union_compatible h0 h1) h2) h3

/-- Every retained record comes from a valid raw four-leaf occurrence, even
if this task overflows. Compatible masks were filtered before the streams. -/
theorem entries_provenance (B : ℕ) (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) :
    ∃ x ∈ RepresentationUniverse.parents D.leaves, RepresentationUniverse.Valid x ∧
      RepresentationUniverse.entry D.weights x = e ∧
        D.maskRestriction.Compatible (RepresentationUniverse.topDomain D.leaves) e.mask := by
  have h0 := (D.pair 0).output_length_le
  have h1 := (D.pair 1).output_length_le
  obtain ⟨x, hx, y, hy, _, hem⟩ := RecordedDictionary.join_provenance D.capacity
    (WeightEncoding.entryKey D.input) (D.pair 0).read (D.key 0) (D.pair 1).read (D.key 1)
    D.emit (D.pair 0).output (D.pair 0).read_law (D.pair 1).output (D.pair 1).read_law
    B _ _ _ (D.pair 0).start (D.pair 1).start (D.pair 0).output_sorted
    (D.pair 1).output_sorted h0 h1 (by omega) e he
  obtain ⟨hv, rfl⟩ := (D.emit_some_iff x y e).mp hem
  exact ⟨(x, y), D.streams_parent x y hx hy, hv, rfl, D.streams_compatible x y hx hy⟩

end RepresentationParentData
end LowSpaceSubsetSum

end OAI
