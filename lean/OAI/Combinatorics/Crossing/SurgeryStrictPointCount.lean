import OAI.Combinatorics.Crossing.SurgeryCrossingContainment
import Mathlib.Data.Set.Card

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  {p q : C.InnerIndex}

theorem crossingChord_meeting_is_assembled_crossing (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  apply crossing_of_ranges_not_vertices (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
    p.1 q.1 (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x
    ((E.assembled_range_in_crossingDisk v hv p x hxin).mpr hxp)
    ((E.assembled_range_in_crossingDisk v hv q x hxinq).mpr hxq)
  intro j he
  exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hxin (he.symm ▸ (hv j).le)

theorem adjacentSurgeryDrawing_strict_crossing_ncard
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    (crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).Finite ∧
      (crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).ncard <
        (crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing).ncard := by
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  have hsub := E.adjacentSurgeryDrawing_crossings_subset v hvinj hv hdet P Kp Kq hpq hm hadj hcross hemb
  have hfinite := (E.assembledAdmissible v hvinj hv hdet).crossings_finite
  have hremoved := adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq (by
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1)
  have hnot : x ∉ crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) := by
    rintro ⟨e,f,hef,hxe,hxf⟩
    exact hremoved e (edgeInterior_subset_range _ e hxe)
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ⟨hsub,?_⟩ hfinite⟩
  intro hrev
  exact hnot (hrev (E.crossingChord_meeting_is_assembled_crossing v hvinj hv hdet hpq x hxp hxq))

end Zarankiewicz.PolygonalExterior

end

end OAI
