import OAI.Combinatorics.Crossing.AffineSubdivisionRefinement

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

def pieceTrace (P : PolygonalParametrization γ) (i : Fin P.pieces) : Set Plane :=
  segment ℝ (γ (P.knot i.castSucc)) (γ (P.knot i.succ))

theorem pieceTrace_parameter (P : PolygonalParametrization γ) (i : Fin P.pieces)
    (x : Plane) (hx : x ∈ P.pieceTrace i) :
    ∃ t : unitInterval, γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=x := by
  rw [pieceTrace,← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,(P.affine i t).trans ?_⟩
  simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

theorem pieceTrace_subset_range (P : PolygonalParametrization γ) (i : Fin P.pieces) :
    P.pieceTrace i ⊆ Set.range γ := by
  intro x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i x hx
  exact ⟨intervalSegment (P.knot i.castSucc) (P.knot i.succ) t,ht⟩

theorem pieceTrace_knot_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : Fin P.pieces) (j : Fin (P.pieces+1))
    (hx : γ (P.knot j) ∈ P.pieceTrace i) :
    γ (P.knot j)=γ (P.knot i.castSucc) ∨ γ (P.knot j)=γ (P.knot i.succ) := by
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i _ hx
  by_cases ht0 : t=0
  · subst t
    simpa [intervalSegment] using Or.inl ht.symm
  by_cases ht1 : t=1
  · subst t
    simpa [intervalSegment] using Or.inr ht.symm
  have hmid := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) t
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have he := hγ ht
  rw [he] at hmid
  exact False.elim (strictMono_no_between_successors P.knot P.increasing i j hmid)

theorem pieceTrace_other_piece_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i ≠ j) (x : Plane)
    (hx : x ∈ P.pieceTrace i) (hy : x ∈ P.pieceTrace j) :
    x=γ (P.knot i.castSucc) ∨ x=γ (P.knot i.succ) := by
  obtain ⟨s,hs⟩ := P.pieceTrace_parameter i x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter j x hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl (by simpa [intervalSegment] using hs.symm)
  by_cases hs1 : s=1
  · subst s
    exact Or.inr (by simpa [intervalSegment] using hs.symm)
  have hsbetween := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) s
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩
  have htbetween := intervalSegment_between (P.knot j.castSucc) (P.knot j.succ) t
    (P.increasing.monotone (by change j.val ≤ j.val+1; omega))
  have he := hγ (hs.trans ht.symm)
  rw [he] at hsbetween
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := P.increasing.monotone (show i.succ ≤ j.castSucc by change i.val+1 ≤ j.val; exact hij)
    exact False.elim (hsbetween.2.not_ge (hgap.trans htbetween.1))
  · have hgap := P.increasing.monotone (show j.succ ≤ i.castSucc by change j.val+1 ≤ i.val; exact hji)
    exact False.elim (hsbetween.1.not_ge (htbetween.2.trans hgap))

end Zarankiewicz.PolygonalParametrization
namespace Zarankiewicz
variable {m n : ℕ}

theorem subdivision_mark_endpoint (D : AdmissibleDrawing m n)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (e : BipartiteEdge m n) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ (P e).pieceTrace i) (hm : x ∈ drawingMarks D.toFiniteIntersectionDrawing) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hmark e t (ht.symm ▸ hm)
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

end Zarankiewicz

end

end OAI
