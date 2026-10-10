import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ParentPrefixSearch

namespace OAI

/-! # One actual residue bucket: left retention and right prefix search -/

namespace LowSpaceSubsetSum

structure RepresentationBucketData (n g : ℕ) where
  left : RepresentationParentData n
  right : RepresentationParentData n
  coordinates : TopCoordinates n g
  topOrder : List (Fin n)

namespace RepresentationBucketData

variable {n g : ℕ} (D : RepresentationBucketData n g)

def target : ℤ := (D.right.input.target : ℤ) -
  weight (fun i => (D.right.input.values i : ℤ)) D.right.signs

def check (families : Fin 4 → Array (Finset (Fin g)))
    (left right : Array (Entry (Fin n))) : Bool :=
  (D.coordinates.check families D.target left.toList right.toList).accepted

/-- The left array is retained while each right task regenerates its own
restricted leaves and streams. An empty or overflowing left task is skipped. -/
def run (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : Bool :=
  let left := (D.left.collect B).state.user
  if left.keys.overflow then false
  else if left.records.isEmpty then false
  else D.right.searchRight B (D.check families left.records) D.topOrder MaskRestriction.empty

theorem sound (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (hweights : D.left.weights = D.right.weights)
    (htop : ∀ j : Fin 2, RepresentationUniverse.topDomain
      (if j = 0 then D.left.leaves else D.right.leaves) = D.coordinates.domain)
    (htlL : Disjoint (RepresentationUniverse.topDomain D.left.leaves)
      (RepresentationUniverse.mixerDomain D.left.leaves))
    (htbL : Disjoint (RepresentationUniverse.topDomain D.left.leaves)
      (RepresentationUniverse.backgroundDomain D.left.leaves))
    (hlbL : Disjoint (RepresentationUniverse.mixerDomain D.left.leaves)
      (RepresentationUniverse.backgroundDomain D.left.leaves))
    (htlR : Disjoint (RepresentationUniverse.topDomain D.right.leaves)
      (RepresentationUniverse.mixerDomain D.right.leaves))
    (htbR : Disjoint (RepresentationUniverse.topDomain D.right.leaves)
      (RepresentationUniverse.backgroundDomain D.right.leaves))
    (hlbR : Disjoint (RepresentationUniverse.mixerDomain D.right.leaves)
      (RepresentationUniverse.backgroundDomain D.right.leaves))
    (hshared : RepresentationUniverse.parentDomain D.left.leaves ∩
      RepresentationUniverse.parentDomain D.right.leaves ⊆ D.coordinates.domain)
    (hsize : D.left.capacity + 1 + (D.right.capacity + 1) ≤ 2 ^ n)
    (hyes : D.run B families = true) : Solvable D.right.input := by
  have htL : RepresentationUniverse.topDomain D.left.leaves = D.coordinates.domain := by
    simpa only [ite_true] using htop 0
  have htR : RepresentationUniverse.topDomain D.right.leaves = D.coordinates.domain := by
    simpa only [show (1 : Fin 2) ≠ 0 from by decide, ite_false] using htop 1
  unfold run at hyes
  dsimp only at hyes
  split at hyes
  · contradiction
  split at hyes
  · contradiction
  apply D.right.searchRight_subset_sum_sound B D.coordinates families (D.left.entries B)
    D.topOrder MaskRestriction.empty (RepresentationUniverse.parentDomain D.left.leaves)
    htR htlR htbR hlbR hshared ?_ ?_ hyes
  · intro e he
    rw [← hweights, ← htL]
    exact D.left.entry_represents B htlL htbL hlbL e he
  · exact (Nat.add_le_add_right (D.left.storage B).1 _).trans hsize

end RepresentationBucketData
end LowSpaceSubsetSum

end OAI
