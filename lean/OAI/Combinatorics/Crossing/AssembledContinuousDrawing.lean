import OAI.Combinatorics.Crossing.AssembledEdge

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spoke_vertex_eq (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (hk : v k ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : k=j := by
  by_contra hkj
  have hd := C.disks_disjoint _ _ (C.vertexMark_injective.ne (Ne.symm hkj))
  exact Set.disjoint_left.mp hd (C.vertex_spoke_range_in_disk v hv j p hk) (hv k).le

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_avoids_vertices (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n)
    (j : BipartiteVertex m n) : v j ∉ Set.range (E.middlePath e) := by
  intro hx
  rcases (E.middlePath_range_iff e (v j)).mp hx with ⟨i,hi,⟨t,ht⟩⟩ | ⟨p,hp,hx⟩
  · exact E.avoids_new_vertices v hv i t j ht
  · exact Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks p j) hx (hv j).le

theorem assembledEdge_vertex_eq (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n)
    (j : BipartiteVertex m n) (hj : v j ∈ Set.range (E.assembledEdge v e)) :
    j=.inl e.1 ∨ j=.inr e.2 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hj
  rcases hj with (hj | hj) | hj
  · exact Or.inl (C.vertex_spoke_vertex_eq v hv _ j (C.startPortAt e) hj)
  · exact False.elim (E.middlePath_avoids_vertices v hv e j hj)
  · rw [endSpoke_range] at hj
    exact Or.inr (C.vertex_spoke_vertex_eq v hv _ j (C.endPortAt e) hj)

theorem assembledEdge_interior_avoids_vertices (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1)
    (j : BipartiteVertex m n) : E.assembledEdge v e t ≠ v j := by
  intro he
  rcases E.assembledEdge_vertex_eq v hv e j ⟨t,he⟩ with rfl | rfl
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).source.symm)
    exact ht.1.ne hh.symm
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).target.symm)
    exact ht.2.ne hh

def assembledDrawing (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hvinj : Function.Injective v) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) :
    ContinuousDrawing m n where
  vertex := v
  vertex_injective := hvinj
  edge := E.assembledEdge v
  edge_injective := E.assembledEdge_injective v hv
  interior_avoids_vertices := E.assembledEdge_interior_avoids_vertices v hv

theorem exists_assembledDrawing (D : FiniteIntersectionDrawing m n) :
    ∃ (C : DrawingPassages D) (E : PolygonalExterior C)
      (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2),
      ∀ e, Function.Injective ((E.assembledDrawing v hvinj hv).edge e) := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨C,E,v,hvinj,hv,E.assembledEdge_injective v hv⟩

end PolygonalExterior
end Zarankiewicz

end

end OAI
