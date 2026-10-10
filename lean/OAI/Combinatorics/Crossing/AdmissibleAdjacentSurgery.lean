import OAI.Combinatorics.Crossing.SurgeryFiniteDrawing

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_admissible_adjacent_surgery (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : AdmissibleDrawing m n, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      crossingCount A < crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let B := E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq
  obtain ⟨A,hpoly,hcount⟩ := finite_intersection_normalization B
  exact ⟨A,hpoly,hcount.trans_lt
    (E.adjacentSurgeryFiniteDrawing_count_lt v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq)⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
