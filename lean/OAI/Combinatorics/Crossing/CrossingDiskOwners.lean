import OAI.Combinatorics.Crossing.OrderedCrossingPorts

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_in_crossingDisk_chord (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : BipartiteEdge m n) (p : C.InnerIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) :
    ∃ r : C.InnerIndex, r.1=e ∧ C.innerMark r=C.innerMark p ∧ x ∈ Set.range (C.crossingChord r) := by
  rcases (E.assembledEdge_range_iff v e x).mp hx with (hx | ⟨i,hi,hx⟩ | ⟨r,hr,hx⟩) | hx
  · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt e) hx))
  · obtain ⟨t,rfl⟩ := hx
    exact False.elim (hxin.not_ge (E.outside_open_disks i t (C.innerMark p)))
  · refine ⟨r,hr,?_,hx⟩
    by_contra hn
    exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
      (C.crossingChord_range_subset_disk r hx) (C.crossingDisk_subset_closed p hxin)
  · rw [endSpoke_range] at hx
    exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt e) hx))

theorem assembled_crossingDisk_owner (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) : e=p.1 ∨ e=q.1 := by
  obtain ⟨r,hr,hrm,hxr⟩ := E.assembled_in_crossingDisk_chord v hv e p x hx hxin
  rcases C.innerIndex_at_mark_pair p q r hpq hm hrm.symm with rfl | rfl
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem assembled_other_edge_avoids_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (Set.range (E.assembledEdge v e)) (C.crossingDisk p) := by
  apply Set.disjoint_left.mpr
  intro x hx hxin
  rcases E.assembled_crossingDisk_owner v hv p q hpq hm e x hx hxin with h | h
  · exact hep h
  · exact heq h

end Zarankiewicz.PolygonalExterior

end

end OAI
