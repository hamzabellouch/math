import OAI.Combinatorics.Crossing.TruncatedChainDirections
import OAI.Combinatorics.Crossing.SegmentClosedIncidence
import OAI.Combinatorics.Crossing.SharedTrackAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_bend_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : 0 < i) (hi' : i < P.pieces) :
    det2 (trackDirection (P.truncatedVertices r) (i-1)) (trackDirection (P.truncatedVertices r) i) ≠ 0 := by
  rw [P.truncated_direction r (i-1) (by omega),P.truncated_direction r i hi',det2_smul_left,det2_smul_right]
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast (i-1)))
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i))
  have h := P.minimum_bend_det_ne_zero hmin (i-1) (by omega)
  simpa only [trackDirection,show i-1+1=i by omega,show i-1+2=i+1 by omega] using h

theorem truncated_offset_avoidance (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin P.pieces,
      ¬ ClosedSegmentsMeet (P.truncatedVertices r i.val) (P.truncatedVertices r (i.val+1))
        (shiftedTrack (P.truncatedVertices r) P.pieces t j.val)
        (shiftedTrack (P.truncatedVertices r) P.pieces t (j.val+1)) := by
  apply exists_shared_track_avoidance_radius (P.truncatedVertices r) P.pieces
    (P.truncated_direction_ne_zero hmin r hr hfirst hlast)
    (P.truncated_bend_ne_zero hmin r hr hfirst hlast)
  intro i j hij
  have hdis : Disjoint (segment ℝ (P.vertices i.val) (P.vertices (i.val+1)))
      (segment ℝ (P.vertices j.val) (P.vertices (j.val+1))) := by
    rcases hij with h | h
    · exact P.minimum_nonadjacent_disjoint hmin i.val j.val h j.isLt
    · exact (P.minimum_nonadjacent_disjoint hmin j.val i.val h i.isLt).symm
  have hfst : r^2 < squaredLength (P.vertices 1-P.vertices 0) := by nlinarith [sq_nonneg r]
  have hlst : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)) := by nlinarith [sq_nonneg r]
  exact not_closedSegmentsMeet_of_disjoint _ _ _ _ (hdis.mono
    (P.truncated_piece_subset r hr hfst hlst i.val i.isLt)
    (P.truncated_piece_subset r hr hfst hlst j.val j.isLt))

end Zarankiewicz.PolygonalChain

end

end OAI
