import OAI.Combinatorics.Crossing.AssembledContinuousDrawing

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middle_exterior_edge_eq (E : PolygonalExterior C) (e : BipartiteEdge m n)
    (i : C.ArcIndex) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨j,hj,hx⟩ | ⟨p,hp,hx⟩
  · have he : j=i := by
      by_contra hji
      exact Set.disjoint_left.mp (E.disjoint j i hji) hx hy
    exact hj.symm.trans (congrArg Sigma.fst he)
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    rcases E.exterior_chord_meeting_parameters i p s t (hs.trans ht.symm) with
      ⟨hi,_,_⟩ | ⟨hi,_,_⟩
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm

theorem middle_spoke_edge_eq (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (j : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : e=p.val.1.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have hm := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rcases hm.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

theorem middle_middle_meeting_chords (E : PolygonalExterior C) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.middlePath f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have he : ∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p) := by
    rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq f i x hy hh).trans hi).symm)
    · exact hh
  have hf : ∃ q : C.InnerIndex, q.1=f ∧ x ∈ Set.range (C.crossingChord q) := by
    rcases (E.middlePath_range_iff f x).mp hy with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq e i x hx hh).trans hi))
    · exact hh
  obtain ⟨p,hp,hxp⟩ := he
  obtain ⟨q,hq,hxq⟩ := hf
  exact ⟨p,q,hp,hq,hxp,hxq⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
