import OAI.Combinatorics.Crossing.AdjacentSurgeryPointRemoval
import OAI.Combinatorics.Crossing.ExtraDrawingSubdivision
import OAI.Combinatorics.Crossing.CrossingDiskOwners

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_adjacentSurgery_continuousDrawing (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : ContinuousDrawing m n, A.vertex=v ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      (∀ e, x ∉ Set.range (A.edge e)) ∧
      (∀ e, e ≠ p.1 → e ≠ q.1 → ∀ t, A.edge e t=E.assembledEdge v e t) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  refine ⟨A,rfl,adjacentSurgeryDrawing_hasFiniteAffineCover Kp Kq hm hpq hadj hv hemb,?_,?_⟩
  · apply adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  · intro e hep heq t
    exact congrArg (fun γ => γ t) (adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq)

end Zarankiewicz.PolygonalExterior

end

end OAI
