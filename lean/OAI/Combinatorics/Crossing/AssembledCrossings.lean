import OAI.Combinatorics.Crossing.MiddleEdgeIncidence
import OAI.Combinatorics.Crossing.CrossingDiskCount

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem vertex_spokes_meeting (C : DrawingPassages D)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (j k : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k))
    (hpq : p.val ≠ q.val) (x : Plane)
    (hx : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val)))
    (hy : x ∈ Set.range (Path.segment (v k) (C.portPoint q.val))) : x=v j := by
  by_cases hjk : j=k
  · subst k
    exact spokes_meet_only_at_center _ _ _ (hdet j p q (fun he => hpq (congrArg Subtype.val he)))
      (by simpa only [Path.range_segment] using hx) (by simpa only [Path.range_segment] using hy)
  · exact False.elim (Set.disjoint_left.mp (C.vertex_spokes_disjoint_of_vertices_ne v hv j k hjk p q) hx hy)

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_spoke_meeting (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (hep : e ≠ p.val.1.1) (x : Plane) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=v j := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · exact C.vertex_spokes_meeting v hv hdet j _ p (C.startPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx
  · exact False.elim (hep (E.middle_spoke_edge_eq v hv e j p x hx hy))
  · rw [endSpoke_range] at hx
    exact C.vertex_spokes_meeting v hv hdet j _ p (C.endPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx

theorem assembled_meeting_chords (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (x : Plane)
    (havoid : ∀ j, x ≠ v j) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (E.assembledEdge v f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have hm (a b : BipartiteEdge m n) (hab : a ≠ b)
      (ha : x ∈ Set.range (E.assembledEdge v a)) (hb : x ∈ Set.range (E.assembledEdge v b)) :
      x ∈ Set.range (E.middlePath a) := by
    rw [assembledEdge,Path.trans_range,Path.trans_range] at ha
    rcases ha with (ha | ha) | ha
    · exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.startPortAt a)
        (Ne.symm hab) x hb ha))
    · exact ha
    · rw [endSpoke_range] at ha
      exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.endPortAt a)
        (Ne.symm hab) x hb ha))
  exact E.middle_middle_meeting_chords e f hef x (hm e f hef hx hy) (hm f e (Ne.symm hef) hy hx)

theorem assembled_crossings_subset (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    crossingPoints (E.assembledDrawing v hvinj hv) ⊆ C.chordCrossings := by
  rintro x ⟨e,f,hef,⟨s,hs,he⟩,⟨t,ht,hf⟩⟩
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq))
    ⟨s,he⟩ ⟨t,hf⟩
  exact ⟨p,q,(fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))),hxp,hxq⟩

theorem assembled_crossings_finite (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    (crossingPoints (E.assembledDrawing v hvinj hv)).Finite :=
  C.chordCrossings_finite.subset (E.assembled_crossings_subset v hvinj hv hdet)

end PolygonalExterior
end Zarankiewicz

end

end OAI
