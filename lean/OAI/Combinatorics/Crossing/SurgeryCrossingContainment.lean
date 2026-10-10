import OAI.Combinatorics.Crossing.SurgeryRouteIntersections
import OAI.Combinatorics.Crossing.ReplaceDrawingRangeCases
import OAI.Combinatorics.Crossing.DrawingRangeCrossings

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

theorem adjacentSurgeryDrawing_crossings_subset
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) ⊆
      crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  let B := (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  intro x hx
  obtain ⟨e,f,hef,hxe,hxf⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hpair (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) : x ∈ crossingPoints B := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hx hy
    exact crossing_of_ranges_not_vertices B p.1 q.1
      (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x hh.1 hh.2 havoid
  have hmixed (g : BipartiteEdge m n) (hgp : g ≠ p.1) (hgq : g ≠ q.1)
      (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (hy : x ∈ Set.range (B.edge g)) : x ∈ crossingPoints B := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj g hgp hgq x hx hy with h | h
    · exact crossing_of_ranges_not_vertices B p.1 g (Ne.symm hgp) x h hy havoid
    · exact crossing_of_ranges_not_vertices B q.1 g (Ne.symm hgq) x h hy havoid
  have hcases (g : BipartiteEdge m n) (hg : x ∈ Set.range (A.edge g)) :=
    B.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) g x hg
  rcases hcases e (edgeInterior_subset_range A e hxe) with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact False.elim (hef (hep.trans hfp.symm))
    · exact hpair hx hy
    · exact hmixed f hfp hfq (Or.inl hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hpair hy hx
    · exact False.elim (hef (heq.trans hfq.symm))
    · exact hmixed f hfp hfq (Or.inr hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hmixed e hep heq (Or.inl hy) hx
    · exact hmixed e hep heq (Or.inr hy) hx
    · exact crossing_of_ranges_not_vertices B e f hef x hx hy havoid

end Zarankiewicz.PolygonalExterior

end

end OAI
