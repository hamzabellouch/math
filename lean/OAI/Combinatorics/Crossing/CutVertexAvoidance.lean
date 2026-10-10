import OAI.Combinatorics.Crossing.ExteriorCrossingCut

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem drawing_edge_vertex_parameter (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (t : unitInterval) (v : BipartiteVertex m n) (he : D.edge e t=D.vertex v) :
    (t=0 ∧ v=.inl e.1) ∨ (t=1 ∧ v=.inr e.2) := by
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨rfl,(D.vertex_injective ((D.edge e).source.symm.trans he)).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inr ⟨rfl,(D.vertex_injective ((D.edge e).target.symm.trans he)).symm⟩
  exact False.elim (D.interior_avoids_vertices e t
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩ v he)

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_lt_one (K : ExteriorCrossingCut C P r) : (P r.1).knot K.first < 1 := by
  rw [← (P r.1).last]
  exact (P r.1).increasing (K.ordered.trans_le (Fin.le_last _))

theorem last_parameter_pos (K : ExteriorCrossingCut C P r) : 0 < (P r.1).knot K.last := by
  rw [← (P r.1).first]
  exact (P r.1).increasing ((Fin.zero_le K.first).trans_lt K.ordered)

theorem prefix_vertex_eq (K : ExteriorCrossingCut C P r) (v : BipartiteVertex m n)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val))) :
    v=.inl r.1.1 := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨_,hv⟩ | ⟨ht1,_⟩
  · exact hv
  · exact False.elim ((ht1 ▸ ht.2).not_gt K.first_parameter_lt_one)

theorem suffix_vertex_eq (K : ExteriorCrossingCut C P r) (v : BipartiteVertex m n)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) :
    v=.inr r.1.2 := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨ht0,_⟩ | ⟨_,hv⟩
  · exact False.elim ((ht0 ▸ ht.1).not_gt K.last_parameter_pos)
  · exact hv

end ExteriorCrossingCut
end Zarankiewicz

end

end OAI
