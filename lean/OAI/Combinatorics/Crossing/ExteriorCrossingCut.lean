import OAI.Combinatorics.Crossing.SurgeryCutWalks

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

structure ExteriorCrossingCut (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (r : C.InnerIndex) where
  first : Fin ((P r.1).pieces+1)
  last : Fin ((P r.1).pieces+1)
  ordered : first < last
  first_point : (drawingEdgeWalk P r.1).getVert first.val=C.portPoint (C.incomingPort r)
  last_point : (drawingEdgeWalk P r.1).getVert last.val=C.portPoint (C.outgoingPort r)
  prefix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take first.val))) (C.crossingDisk r)
  suffix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop last.val))) (C.crossingDisk r)

theorem PolygonalExterior.nonempty_exteriorCrossingCut {C : DrawingPassages D.toFiniteIntersectionDrawing} (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (r : C.InnerIndex) : Nonempty (ExteriorCrossingCut C P r) := by
  obtain ⟨i,j,hij,hi,hj,hout,hout'⟩ := E.exists_exterior_crossing_cuts v hvinj hv hdet P hport r
  exact ⟨⟨i,j,hij,hi,hj,hout,hout'⟩⟩

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q r : C.InnerIndex}

def prefixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex (.inl r.1.1)) (C.portPoint (C.incomingPort r)) :=
  surgeryPrefixWalk C P p q r K.first.val K.first_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.prefix_outside)

def suffixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex (.inr r.1.2)) :=
  surgerySuffixWalk C P p q r K.last.val K.last_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.suffix_outside)

theorem prefixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.prefixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) :=
  surgeryPrefixWalk_trace _ _ _ _ _ _ _ _

theorem suffixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.suffixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) :=
  surgerySuffixWalk_trace _ _ _ _ _ _ _ _

end ExteriorCrossingCut
end Zarankiewicz

end

end OAI
