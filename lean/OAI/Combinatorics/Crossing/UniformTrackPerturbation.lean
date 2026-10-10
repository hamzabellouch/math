import OAI.Combinatorics.Crossing.TruncatedTrackStability
import OAI.Combinatorics.Crossing.PolygonalWalks

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_all_edge_shift_radius (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          if e=f then 0 else segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  obtain ⟨δ₀,hδ₀,hother⟩ := V.exists_distinct_edge_shift_radius hnorm hstraight htrans
  choose radius hpos hself using V.offset_avoidance
  obtain ⟨δ₁,hδ₁,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun e _ => hpos e)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro t ht hsmall e f i j
  by_cases hef : e=f
  · subst f
    have hno := hself e t ht ((hsmall.trans_le (min_le_right _ _)).trans (hbound e (Finset.mem_univ _))) i j
    refine ⟨?_,?_⟩
    · intro s hs u hu he
      exact False.elim (hno ⟨s,hs,u,hu,he⟩)
    · have hp : ¬ SegmentsCrossProperly (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
          (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
        fun h => hno (closedSegmentsMeet_of_proper _ _ _ _ h)
      simp [segmentCrossingSign,hp]
  · obtain ⟨hT,hS⟩ := hother t (hsmall.trans_le (min_le_left _ _)) e f hef i j
    exact ⟨hT,by simpa only [ite_eq_right hef] using hS⟩

theorem exists_uniform_track_intersections (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) t) (V.pieces e) (V.pieces f) =
        if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := V.exists_all_edge_shift_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall e f
  by_cases hef : e=f
  · rw [ite_eq_left hef]
    unfold polygonIntersection
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simpa only [ite_eq_left hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2
  · rw [ite_eq_right hef]
    unfold polygonIntersection
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [ite_eq_right hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2

end Zarankiewicz.VertexTruncation

end

end OAI
