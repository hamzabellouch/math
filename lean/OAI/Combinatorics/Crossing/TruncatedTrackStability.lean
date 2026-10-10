import OAI.Combinatorics.Crossing.VertexTruncationGeometry

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_distinct_edge_shift_radius (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ e f : BipartiteEdge m n, e ≠ f →
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  let Pair := Σ e : BipartiteEdge m n, Σ f : {f : BipartiteEdge m n // e ≠ f},
    Fin (V.pieces e) × Fin (V.pieces f.val)
  let a : Pair → Plane := fun k => V.vertices k.1 k.2.2.1.val
  let b : Pair → Plane := fun k => V.vertices k.1 (k.2.2.1.val+1)
  let c : Pair → Plane := fun k => V.vertices k.2.1.val k.2.2.2.val
  let d : Pair → Plane := fun k => V.vertices k.2.1.val (k.2.2.2.val+1)
  let qc : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) k.2.2.2.val
  let qd : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) (k.2.2.2.val+1)
  have hh (k : Pair) : SegmentPairTransverse (a k) (b k) (c k) (d k) :=
    V.pair_transverse hnorm hstraight htrans k.1 k.2.1.val k.2.1.property k.2.2.1 k.2.2.2
  obtain ⟨δ,hδ,hstable⟩ := exists_shifted_segment_pairs_radius a b c d qc qd hh
  refine ⟨δ,hδ,?_⟩
  intro t ht e f hef i j
  exact hstable t ht ⟨e,⟨f,hef⟩,i,j⟩

end Zarankiewicz.VertexTruncation

end

end OAI
