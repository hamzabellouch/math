import OAI.Combinatorics.Crossing.AssembledNoTriples

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def crossingDisk (C : DrawingPassages D) (p : C.InnerIndex) : Set Plane :=
  {x | squaredLength (x-(C.innerMark p).val) < C.radius^2}

theorem crossingDisk_isOpen (C : DrawingPassages D) (p : C.InnerIndex) : IsOpen (C.crossingDisk p) := by
  apply isOpen_lt _ continuous_const
  unfold squaredLength
  fun_prop

theorem crossingDisk_subset_closed (C : DrawingPassages D) (p : C.InnerIndex) :
    C.crossingDisk p ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  exact (show squaredLength (x-(C.innerMark p).val) < C.radius^2 from hx).le

theorem crossingDisk_disjoint_vertex_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (j : BipartiteVertex m n) :
    Disjoint (C.crossingDisk p) (closedRoundDisk (D.vertex j) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingDisk_subset_closed p) Set.Subset.rfl

theorem crossingChord_openTrace_iff (C : DrawingPassages D) (p : C.InnerIndex)
    (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (C.crossingChord p) ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  constructor
  · rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      rw [Path.source] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.incomingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      rw [Path.target] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.outgoingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    refine ⟨t.val,⟨?_,?_⟩,?_⟩
    · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    · simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,ht.1.le,ht.2.le⟩,?_⟩
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_range_in_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (E.assembledEdge v p.1) ↔ x ∈ Set.range (C.crossingChord p) := by
  constructor
  · intro he
    rcases (E.assembledEdge_range_iff v p.1 x).mp he with (he | ⟨i,hi,he⟩ | ⟨q,hq,he⟩) | he
    · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt p.1) he))
    · obtain ⟨t,rfl⟩ := he
      exact False.elim (hx.not_ge (E.outside_open_disks i t (C.innerMark p)))
    · have hm : C.innerMark q=C.innerMark p := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
          (C.crossingChord_range_subset_disk q he) (C.crossingDisk_subset_closed p hx)
      have hqp := C.innerIndex_eq_of_edge_mark q p hq hm
      exact hqp ▸ he
    · rw [endSpoke_range] at he
      exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt p.1) he))
  · intro he
    apply (E.assembledEdge_range_iff v p.1 x).mpr
    exact Or.inl (Or.inr (Or.inr ⟨p,rfl,he⟩))

theorem assembled_trace_in_crossingDisk (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ edgeInterior (E.assembledDrawing v hvinj hv) p.1 ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  have havoid : ∀ j, x ≠ v j := by
    intro j he
    exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hx (he.symm ▸ (hv j).le)
  rw [← C.crossingChord_openTrace_iff p x hx,← E.assembled_range_in_crossingDisk v hv p x hx]
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨t,he⟩
  · rintro ⟨t,he⟩
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      rw [Path.source] at he
      exact havoid _ he.symm
    have ht1 : t ≠ 1 := by
      intro ht
      subst t
      rw [Path.target] at he
      exact havoid _ he.symm
    exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

end PolygonalExterior
end Zarankiewicz

end

end OAI
