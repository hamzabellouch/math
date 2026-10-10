import OAI.Combinatorics.Crossing.ReconnectedWalks

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def reconnectedForwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex (.inl p.1.1)) (D'.vertex (.inr q.1.2)) := by
  classical
  exact graphWalkPath id (reconnectedForwardWalk Kp Kq hm).bypass

def reconnectedBackwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex (.inl q.1.1)) (D'.vertex (.inr p.1.2)) := by
  classical
  exact graphWalkPath id (reconnectedBackwardWalk Kp Kq hm).bypass

theorem reconnectedForwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C p q)
    _ (reconnectedForwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedBackwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C q p)
    _ (reconnectedBackwardWalk Kp Kq hm).bypass_isPath

theorem reconnectedForwardPath_hasFiniteAffineCover (Kp : ExteriorCrossingCut C P p)
    (Kq : ExteriorCrossingCut C P q) (hm : C.innerMark p=C.innerMark q) :
    HasFiniteAffineCover (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_hasFiniteAffineCover id _

theorem reconnectedBackwardPath_hasFiniteAffineCover (Kp : ExteriorCrossingCut C P p)
    (Kq : ExteriorCrossingCut C P q) (hm : C.innerMark p=C.innerMark q) :
    HasFiniteAffineCover (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_hasFiniteAffineCover id _

theorem reconnectedForwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedForwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedForwardWalk Kp Kq hm)).trans
    (by rw [reconnectedForwardWalk_trace])

theorem reconnectedBackwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedBackwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedBackwardWalk Kp Kq hm)).trans
    (by rw [reconnectedBackwardWalk_trace])

end Zarankiewicz

end

end OAI
