import OAI.Combinatorics.Crossing.ExteriorCrossingCut
import OAI.Combinatorics.Crossing.SurgeryPathWitnesses

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem surgery_forward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)) :=
  crossingSurgeryGraph_reconnection_adj C P p q true

theorem surgery_backward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)) :=
  crossingSurgeryGraph_reconnection_adj C P p q false

def reconnectedForwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl p.1.1)) (D'.vertex (.inr q.1.2)) :=
  walkThroughChord (Kp.prefixInSurgery p q rfl)
    surgery_forward_adj (Kq.suffixInSurgery p q hm.symm)

def reconnectedBackwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl q.1.1)) (D'.vertex (.inr p.1.2)) :=
  walkThroughChord (Kq.prefixInSurgery p q hm.symm)
    surgery_backward_adj (Kp.suffixInSurgery p q rfl)

theorem reconnectedForwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedForwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  rw [reconnectedForwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

theorem reconnectedBackwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedBackwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  rw [reconnectedBackwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]

end Zarankiewicz

end

end OAI
