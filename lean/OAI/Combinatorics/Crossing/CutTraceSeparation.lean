import OAI.Combinatorics.Crossing.CutVertexAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz.ExteriorCrossingCut
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.first)=C.portPoint (C.incomingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.first.val (by have h := K.first.isLt; omega)).trans
    ((P r.1).vertices_at K.first)).symm.trans K.first_point

theorem last_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.last)=C.portPoint (C.outgoingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.last.val (by have h := K.last.isLt; omega)).trans
    ((P r.1).vertices_at K.last)).symm.trans K.last_point

theorem prefix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  exact ⟨t,he⟩

theorem suffix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  exact ⟨t,he⟩

theorem incoming_not_suffix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.incomingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  have heq := D'.edge_injective r.1 (he.trans K.first_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.1)

theorem outgoing_not_prefix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.outgoingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  have heq := D'.edge_injective r.1 (he.trans K.last_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.2)

theorem prefix_suffix_disjoint (K : ExteriorCrossingCut C P r) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  obtain ⟨u,hu,hf⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hy
  have heq := D'.edge_injective r.1 (he.trans hf.symm)
  exact ((P r.1).increasing K.ordered).not_ge (hu.1.trans (heq ▸ ht.2))

end Zarankiewicz.ExteriorCrossingCut

end

end OAI
