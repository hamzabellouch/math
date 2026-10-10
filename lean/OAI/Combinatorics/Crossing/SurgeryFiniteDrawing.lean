import OAI.Combinatorics.Crossing.SurgeryNoTriples
import OAI.Combinatorics.Crossing.SurgeryStrictPointCount

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

def adjacentSurgeryFiniteDrawing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    FiniteIntersectionDrawing m n where
  toContinuousDrawing := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  crossings_finite := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).1
  no_triples := E.adjacentSurgeryDrawing_no_triples v hvinj hv hdet P Kp Kq hpq hm hadj
    (C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq) hemb

theorem adjacentSurgeryFiniteDrawing_count_lt
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    finiteCrossingCount (E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq) <
      crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  rw [finiteCrossingCount_eq_ncard]
  have h := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).2
  exact h.trans_eq (Set.ncard_eq_toFinset_card _ (E.assembledAdmissible v hvinj hv hdet).crossings_finite)

end Zarankiewicz.PolygonalExterior

end

end OAI
