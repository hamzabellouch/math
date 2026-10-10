import OAI.Combinatorics.Crossing.SubdivisionSegments
import OAI.Combinatorics.Crossing.EmbeddedGraphPaths

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawing_curve_meeting_mark (D : AdmissibleDrawing m n) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hy : x ∈ Set.range (D.edge f)) :
    x ∈ drawingMarks D.toFiniteIntersectionDrawing := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl ⟨.inl e.1,by simpa using hs⟩
  by_cases hs1 : s=1
  · subst s
    exact Or.inl ⟨.inr e.2,by simpa using hs⟩
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨.inl f.1,by simpa using ht⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inl ⟨.inr f.2,by simpa using ht⟩
  exact Or.inr ⟨e,f,hef,
    ⟨s,⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩,hs⟩,
    ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,ht⟩⟩

abbrev DrawingPiece {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e)) :=
  (e : BipartiteEdge m n) × Fin (P e).pieces

def drawingPieceStart {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.castSucc)

def drawingPieceEnd {D : AdmissibleDrawing m n} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.succ)

theorem drawingPiece_endpoints_ne {D : AdmissibleDrawing m n}
    (P : ∀ e, PolygonalParametrization (D.edge e)) (i : DrawingPiece P) :
    drawingPieceStart P i ≠ drawingPieceEnd P i := by
  intro he
  have hh := D.edge_injective i.1 he
  exact ((P i.1).increasing (show i.2.castSucc < i.2.succ by change i.2.val < i.2.val+1; omega)).ne hh

theorem drawing_pieces_meeting_endpoints (D : AdmissibleDrawing m n)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (p q : DrawingPiece P) (hpq : p ≠ q) (x : Plane)
    (hx : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p))
    (hy : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q)) :
    (x=drawingPieceStart P p ∨ x=drawingPieceEnd P p) ∧
      (x=drawingPieceStart P q ∨ x=drawingPieceEnd P q) := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  by_cases hef : e=f
  · subst f
    have hij : i ≠ j := fun he => hpq (by subst j; rfl)
    exact ⟨(P e).pieceTrace_other_piece_endpoint (D.edge_injective e) i j hij x hx hy,
      (P e).pieceTrace_other_piece_endpoint (D.edge_injective e) j i (Ne.symm hij) x hy hx⟩
  · have hm := drawing_curve_meeting_mark D e f hef x
      ((P e).pieceTrace_subset_range i hx) ((P f).pieceTrace_subset_range j hy)
    exact ⟨subdivision_mark_endpoint D P hmark e i x hx hm,
      subdivision_mark_endpoint D P hmark f j x hy hm⟩

end Zarankiewicz

end

end OAI
