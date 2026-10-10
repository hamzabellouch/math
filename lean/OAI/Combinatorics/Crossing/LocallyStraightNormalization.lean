import OAI.Combinatorics.Crossing.PolygonalNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def LocallyStraightAt (D : ContinuousDrawing m n) (e : BipartiteEdge m n) (x : Plane) : Prop :=
  ∃ a b : Plane, a ≠ b ∧ x ∈ openSegmentTrace a b ∧
    ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ edgeInterior D e ↔ z ∈ openSegmentTrace a b

def LocallyStraightCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → ∀ x,
    x ∈ edgeInterior D.toContinuousDrawing e → x ∈ edgeInterior D.toContinuousDrawing f →
      LocallyStraightAt D.toContinuousDrawing e x ∧ LocallyStraightAt D.toContinuousDrawing f x

namespace PolygonalExterior
variable {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_locallyStraightCrossings (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyStraightCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  intro e f hef x hx hy
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hpx := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hqx := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  have hlocal (r : C.InnerIndex) (hr : x ∈ C.crossingDisk r)
      (hxr : x ∈ Set.range (C.crossingChord r)) :
      LocallyStraightAt (E.assembledDrawing v hvinj hv) r.1 x := by
    refine ⟨C.portPoint (C.incomingPort r),C.portPoint (C.outgoingPort r),
      C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort r r),
      (C.crossingChord_openTrace_iff r x hr).mp hxr,C.crossingDisk r,C.crossingDisk_isOpen r,hr,?_⟩
    exact E.assembled_trace_in_crossingDisk v hvinj hv r
  change LocallyStraightAt (E.assembledDrawing v hvinj hv) e x ∧
    LocallyStraightAt (E.assembledDrawing v hvinj hv) f x
  exact ⟨by simpa only [hp] using hlocal p hpx hxp,by simpa only [hq] using hlocal q hqx hxq⟩

end PolygonalExterior

theorem polygonal_normalization_locally_straight (D : AdmissibleDrawing m n) :
    ∃ D' : AdmissibleDrawing m n, crossingCount D' ≤ crossingCount D ∧
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ LocallyStraightCrossings D' := by
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembled_crossingCount_le v hvinj hv hdet,
    E.assembledEdge_hasFiniteAffineCover v,E.assembled_locallyStraightCrossings v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
