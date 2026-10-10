import OAI.Combinatorics.Crossing.AssembledCrossings

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem portPoint_mem_exterior (E : PolygonalExterior C) (p : C.Port) :
    C.portPoint p ∈ Set.range (E.chain p.1).path := by
  rcases p with ⟨i,b⟩
  cases b
  · exact ⟨0,(E.chain i).path.source⟩
  · exact ⟨1,(E.chain i).path.target⟩

theorem assembled_port_mem_range (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (p : C.Port) : C.portPoint p ∈ Set.range (E.assembledEdge v p.1.1) := by
  apply (E.assembledEdge_range_iff v p.1.1 (C.portPoint p)).mpr
  exact Or.inl (Or.inr (Or.inl ⟨p.1,rfl,E.portPoint_mem_exterior p⟩))

theorem assembled_exterior_edge_eq (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.startPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
  · exact E.middle_exterior_edge_eq e i x hx hy
  · rw [endSpoke_range] at hx
    obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.endPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm

theorem assembled_port_unique_edge (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (p : C.Port)
    (hp : C.portPoint p ∈ Set.range (E.assembledEdge v e)) : e=p.1.1 :=
  E.assembled_exterior_edge_eq v hv e p.1 (C.portPoint p) hp (E.portPoint_mem_exterior p)

end Zarankiewicz.PolygonalExterior

end

end OAI
