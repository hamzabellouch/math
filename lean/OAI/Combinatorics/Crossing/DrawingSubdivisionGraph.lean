import OAI.Combinatorics.Crossing.DrawingSegmentIncidence

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

def drawingSubdivisionGraph (P : ∀ e, PolygonalParametrization (D.edge e)) : SimpleGraph Plane where
  Adj := fun a b => a ≠ b ∧ ∃ p : DrawingPiece P,
    (a=drawingPieceStart P p ∧ b=drawingPieceEnd P p) ∨
      (a=drawingPieceEnd P p ∧ b=drawingPieceStart P p)
  symm := ⟨by
    rintro a b ⟨hab,p,hp⟩
    refine ⟨Ne.symm hab,p,?_⟩
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩

theorem drawingSubdivisionGraph_piece_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (p : DrawingPiece P) :
    (drawingSubdivisionGraph P).Adj (drawingPieceStart P p) (drawingPieceEnd P p) :=
  ⟨drawingPiece_endpoints_ne P p,p,Or.inl ⟨rfl,rfl⟩⟩

theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))

theorem drawingSubdivisionGraph_embedding (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) :
    StraightEdgeEmbedding (drawingSubdivisionGraph P) id := by
  refine ⟨Function.injective_id,?_⟩
  rintro a b c d ⟨hab,p,hp⟩ ⟨hcd,q,hq⟩ x hx hy
  by_cases hpq : p=q
  · subst q
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inl ⟨rfl,rfl⟩
  · have hxp : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · simpa only [id_eq,segment_symm] using hx
    have hxq : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q) := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · simpa only [id_eq,segment_symm] using hy
    obtain ⟨hpe,hqe⟩ := drawing_pieces_meeting_endpoints D P hmark p q hpq x hxp hxq
    have heab : x=a ∨ x=b := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpe
      · exact hpe.symm
    have hecd : x=c ∨ x=d := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hqe
      · exact hqe.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives a b c d x heab hecd))

theorem drawingSubdivisionGraph_finite_support (P : ∀ e, PolygonalParametrization (D.edge e)) :
    {a : Plane | ∃ b, (drawingSubdivisionGraph P).Adj a b}.Finite := by
  have hf : (Set.range (drawingPieceStart P) ∪ Set.range (drawingPieceEnd P)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  apply hf.subset
  rintro a ⟨b,hab,p,hp⟩
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨p,ha.symm⟩
  · exact Or.inr ⟨p,ha.symm⟩

end Zarankiewicz

end

end OAI
