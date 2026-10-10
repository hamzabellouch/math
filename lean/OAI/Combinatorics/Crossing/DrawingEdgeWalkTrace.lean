import OAI.Combinatorics.Crossing.DrawingEdgeWalk
import OAI.Combinatorics.Crossing.OrderedKnotCover

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

theorem range_pieceTrace_iff (P : PolygonalParametrization γ) (x : Plane) :
    x ∈ Set.range γ ↔ ∃ i : Fin P.pieces, x ∈ P.pieceTrace i := by
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨i,hi⟩ := P.knot_cover u
    obtain ⟨t,ht⟩ := intervalSegment_surjective_interval (P.knot i.castSucc) (P.knot i.succ)
      (P.increasing (by change i.val < i.val+1; omega)) u hi
    refine ⟨i,?_⟩
    rw [pieceTrace,← Path.range_segment]
    refine ⟨t,?_⟩
    have he := (P.affine i t).symm.trans (congrArg γ ht)
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
  · rintro ⟨i,hi⟩
    exact P.pieceTrace_subset_range i hi

end Zarankiewicz.PolygonalParametrization
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem drawingEdgeWalk_range_eq (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) :
    Set.range (graphWalkPath id (drawingEdgeWalk P e))=Set.range (D.edge e) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hlen := drawingEdgeWalk_length P e
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (fun i => (drawingEdgeWalk P e).getVert i)
      (drawingEdgeWalk P e).length (by rw [hlen]; exact (P e).pieces_pos) x hx
    rw [hlen] at hi
    rw [drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hi⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    exact (P e).pieceTrace_subset_range j hxi
  · intro x hx
    obtain ⟨i,hi⟩ := ((P e).range_pieceTrace_iff x).mp hx
    apply polygonalArcPath_piece_subset_range (fun j => (drawingEdgeWalk P e).getVert j)
      (drawingEdgeWalk P e).length i.val (by rw [drawingEdgeWalk_length]; exact i.isLt)
    rw [drawingEdgeWalk_getVert P e i.val (by omega),drawingEdgeWalk_getVert P e (i.val+1) (by omega)]
    have h0 : (P e).vertices i.val=D.edge e ((P e).knot i.castSucc) := (P e).vertices_at i.castSucc
    have h1 : (P e).vertices (i.val+1)=D.edge e ((P e).knot i.succ) := (P e).vertices_at i.succ
    rw [h0,h1]
    exact hi

end Zarankiewicz

end

end OAI
