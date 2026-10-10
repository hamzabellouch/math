import OAI.Combinatorics.Crossing.TruncatedTrackAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def truncated (P : PolygonalChain O a b) (hp : 0 < P.pieces) (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    PolygonalChain O (P.startPort r) (P.endPort r) where
  pieces := P.pieces
  vertices := P.truncatedVertices r
  first := P.truncatedVertices_first r
  last := P.truncatedVertices_last hp r
  start_mem := P.inside 0 hp (openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment _ _ r hr hfirst))
  inside := fun i hi => (P.truncated_piece_subset r hr hfirst hlast i hi).trans (P.inside i hi)

theorem truncated_segments_disjoint (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i j : ℕ) (hij : i+1 < j) (hj : j < P.pieces) :
    Disjoint (segment ℝ (P.truncatedVertices r i) (P.truncatedVertices r (i+1)))
      (segment ℝ (P.truncatedVertices r j) (P.truncatedVertices r (j+1))) :=
  (P.minimum_nonadjacent_disjoint hmin i j hij hj).mono
    (P.truncated_piece_subset r hr hfirst hlast i (by omega))
    (P.truncated_piece_subset r hr hfirst hlast j hj)

theorem truncated_path_injective (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    Function.Injective (polygonalArcPath (P.truncatedVertices r) P.pieces) := by
  have hs : r^2 < squaredLength (P.vertices 1-P.vertices 0) := by nlinarith [sq_nonneg r]
  have ht : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)) := by nlinarith [sq_nonneg r]
  apply polygonalArcPath_injective (P.truncatedVertices r) P.pieces hp
  · intro i hi
    exact Ne.symm (sub_ne_zero.mp (P.truncated_direction_ne_zero hmin r hr hfirst hlast i hi))
  · intro i j hij hj x hx hy
    by_cases he : j=i+1
    · subst j
      refine ⟨rfl,?_⟩
      have hb := P.truncated_bend_ne_zero hmin r hr hfirst hlast (i+1) (by omega) hj
      apply adjacent_segments_meet_only_at_bend _ _ _ ?_ hx hy
      simpa only [trackDirection,Nat.add_sub_cancel] using hb
    · exact False.elim (Set.disjoint_left.mp (P.truncated_segments_disjoint hmin r hr hs ht i j (by omega) hj) hx hy)

end Zarankiewicz.PolygonalChain

end

end OAI
