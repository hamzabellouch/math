import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedReaderContext

namespace OAI

namespace LowSpaceSubsetSum.PreparedReaderContext

variable {n : ℕ}

theorem build_depth (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (j : Fin 2)
    (hL : (D.pair j).left.occurrences.card ≤ 2 ^ n) :
    (build D F P hF j).1.depth ≤ n := by
  have hs := RepresentationStoredArrays.prepare_sizes
    {D with maskRestriction := P.semantic} F P.ones P.zeros j
  change Nat.clog 2
    (RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic}
      F P.ones P.zeros j).1.1.size ≤ n
  exact Nat.clog_le_of_le_pow (hs.1.trans hL)

theorem build_right_size (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (j : Fin 2) :
    (build D F P hF j).1.right.size ≤ (D.pair j).right.occurrences.card := by
  exact (RepresentationStoredArrays.prepare_sizes
    {D with maskRestriction := P.semantic} F P.ones P.zeros j).2

end LowSpaceSubsetSum.PreparedReaderContext

end OAI
