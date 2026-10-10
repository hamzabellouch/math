import OAI.Combinatorics.Crossing.DrawingSubdivisionGraph

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem subdivision_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (e : BipartiteEdge m n) (i : Fin (P e).pieces) (hx : x ∈ (P e).pieceTrace i) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hpoint e t ht
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

theorem drawingSubdivisionGraph_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (a b : Plane) (hab : (drawingSubdivisionGraph P).Adj a b) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b := by
  obtain ⟨hab,p,hp⟩ := hab
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact subdivision_point_endpoint P x hpoint p.1 p.2 hx
  · have hx' : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      simpa only [segment_symm] using hx
    exact (subdivision_point_endpoint P x hpoint p.1 p.2 hx').symm

end Zarankiewicz

end

end OAI
