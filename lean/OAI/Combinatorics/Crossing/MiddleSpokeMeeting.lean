import OAI.Combinatorics.Crossing.MiddlePathInjective
import OAI.Combinatorics.Crossing.ExteriorSpokeMeeting

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spoke_range_in_disk (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j)) :
    Set.range (Path.segment (v j) (C.portPoint p.val)) ⊆ closedRoundDisk (D.vertex j) C.radius := by
  rintro x ⟨t,rfl⟩
  by_cases ht : t=1
  · subst t
    rw [Path.target]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le
  · exact (C.vertex_spoke_interior v hv j p t
      (lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht)).le

theorem vertex_spokes_disjoint_of_vertices_ne (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : BipartiteVertex m n) (hjk : j ≠ k)
    (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k)) :
    Disjoint (Set.range (Path.segment (v j) (C.portPoint p.val)))
      (Set.range (Path.segment (v k) (C.portPoint q.val))) :=
  (C.disks_disjoint _ _ (C.vertexMark_injective.ne hjk)).mono
    (C.vertex_spoke_range_in_disk v hv j p) (C.vertex_spoke_range_in_disk v hv k q)

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middle_spoke_meeting (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=C.portPoint p.val := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have he := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rw [he.1,Path.target] at ht
    exact ht.symm
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

def anchoredMiddle (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Path (C.arcStart (C.firstArc e)) (C.arcEnd (C.lastArc e)) :=
  (E.middlePath e).cast (congrArg C.arcStart (C.orderedArc_first e).symm)
    (congrArg C.arcEnd (C.orderedArc_last e).symm)

theorem anchoredMiddle_range (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Set.range (E.anchoredMiddle e)=Set.range (E.middlePath e) := rfl

theorem anchoredMiddle_injective (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Function.Injective (E.anchoredMiddle e) := E.middlePath_injective e

end PolygonalExterior
end Zarankiewicz

end

end OAI
