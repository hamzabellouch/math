import OAI.Combinatorics.Crossing.ConstructAdjacentSurgery

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_disjoint_of_open_containment (a b : Plane) (U S : Set Plane)
    (hin : openSegmentTrace a b ⊆ U) (hout : Disjoint S U)
    (ha : a ∉ S) (hb : b ∉ S) : Disjoint (segment ℝ a b) S := by
  apply Set.disjoint_left.mpr
  intro x hx hs
  rcases segment_endpoint_or_open a b x hx with rfl | rfl | hx
  · exact ha hs
  · exact hb hs
  · exact Set.disjoint_left.mp hout hs (hin hx)

namespace PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_port_not_mem_other_edge (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (r : C.Port) (her : e ≠ r.1.1) :
    C.portPoint r ∉ Set.range (E.assembledEdge v e) :=
  fun hx => her (E.assembled_port_unique_edge v hv e r hx)

theorem reconnection_other_edge_disjoint (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (i : Bool) (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (Set.range (E.assembledEdge v e)) := by
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm i)
    (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort q) heq
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort p) hep
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort p) hep
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort q) heq

end PolygonalExterior
end Zarankiewicz

end

end OAI
