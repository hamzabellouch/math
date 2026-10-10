import OAI.Combinatorics.Crossing.ExteriorChordMeeting
import OAI.Combinatorics.Crossing.VertexEndpointPorts

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem exterior_spoke_meeting_parameters (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (i : C.ArcIndex) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (s t : unitInterval) (he : (E.chain i).path s=(Path.segment (v j) (C.portPoint p.val)) t) :
    t=1 ∧ ((s=0 ∧ (i,false)=p.val) ∨ (s=1 ∧ (i,true)=p.val)) := by
  have ht : t=1 := by
    apply le_antisymm (show t ≤ 1 from t.property.2)
    apply le_of_not_gt
    intro ht1
    have hinside := C.vertex_spoke_interior v hv j p t ht1
    have hout := E.outside_open_disks i s (C.vertexMark j)
    rw [he] at hout
    exact hinside.not_ge hout
  subst t
  rw [Path.target] at he
  have hs := E.parameter_endpoint_of_mem_disk i s (C.vertexMark j) (by
    rw [he]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le)
  refine ⟨rfl,?_⟩
  rcases hs with rfl | rfl
  · rw [Path.source] at he
    exact Or.inl ⟨rfl,C.portPoint_injective he⟩
  · rw [Path.target] at he
    exact Or.inr ⟨rfl,C.portPoint_injective he⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
