import OAI.Combinatorics.Crossing.CrossingSurgeryGraph
import OAI.Combinatorics.Crossing.CrossingCutWalks
import OAI.Combinatorics.Crossing.GraphWalkRealizationLaws

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

def surgeryPrefixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl r.1.1)) (C.portPoint (C.incomingPort r)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).take i) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy rfl hi

def surgerySuffixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex (.inr r.1.2)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).drop j) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy hj rfl

theorem surgeryPrefixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgeryPrefixWalk C P p q r i hi hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i)) := by
  rw [surgeryPrefixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

theorem surgerySuffixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgerySuffixWalk C P p q r j hj hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j)) := by
  rw [surgerySuffixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

end Zarankiewicz

end

end OAI
