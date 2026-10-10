import OAI.Combinatorics.Crossing.OrderedExteriorPaths

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_injective (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    Function.Injective (E.middlePath e) := by
  have hc := C.count_pos e
  apply alternatingPath_injective
  · intro i hi
    exact E.injective _
  · intro j hj
    have h := C.crossingChord_injective (C.orderedInner e j (by omega))
    intro s t he
    apply h
    simpa only [orderedBridge_apply (C:=C) e j (by omega)] using he
  · intro i j hi hj hij
    exact E.disjoint _ _ (fun he => hij (C.orderedArc_inj e i j (by omega) (by omega) he))
  · intro i j hi hj hij
    rw [orderedBridge_range e i (by omega),orderedBridge_range e j (by omega)]
    apply C.crossingChords_disjoint_of_marks_ne
    intro he
    apply hij
    apply C.orderedInner_inj e i j
    exact C.innerIndex_eq_of_edge_mark _ _ rfl he
  · intro i j hi hj x hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    have hbridge := orderedBridge_apply (C:=C) e j (by omega) t
    have hm := E.exterior_chord_meeting_parameters (C.orderedArc e i)
      (C.orderedInner e j (by omega)) s t (hs.trans (ht.symm.trans hbridge))
    rcases hm with ⟨he,rfl,rfl⟩ | ⟨he,rfl,rfl⟩
    · rw [C.orderedInner_incoming] at he
      have hij := C.orderedArc_inj e i j (by omega) (by omega) he
      refine Or.inl ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e j).target
    · rw [C.orderedInner_outgoing] at he
      have hij := C.orderedArc_inj e i (j+1) (by omega) (by omega) he
      refine Or.inr ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e (j+1)).source

theorem middlePath_range_iff (E : PolygonalExterior C) (e : BipartiteEdge m n) (x : Plane) :
    x ∈ Set.range (E.middlePath e) ↔
      (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
      (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p)) := by
  have hc := C.count_pos e
  rw [middlePath,alternatingPath_range_iff]
  constructor
  · rintro (⟨i,hi,hx⟩ | ⟨j,hj,hx⟩)
    · exact Or.inl ⟨C.orderedArc e i,rfl,hx⟩
    · exact Or.inr ⟨C.orderedInner e j (by omega),rfl,
        by simpa only [orderedBridge_range (C:=C) e j (by omega)] using hx⟩
  · rintro (⟨⟨f,i⟩,he,hx⟩ | ⟨⟨f,⟨j,hj⟩⟩,he,hx⟩)
    · change f=e at he
      subst f
      refine Or.inl ⟨i.val,by omega,?_⟩
      have heq : C.orderedArc e i.val=⟨e,i⟩ := by
        unfold DrawingPassages.orderedArc
        congr 1
        apply Fin.ext
        change min i.val (C.count e-1)=i.val
        omega
      change x ∈ Set.range (E.chain (C.orderedArc e i.val)).path
      rw [heq]
      exact hx
    · change f=e at he
      subst f
      refine Or.inr ⟨j.val-1,by omega,?_⟩
      rw [orderedBridge_range e (j.val-1) (by omega)]
      have heq : C.orderedInner e (j.val-1) (by omega)=⟨e,⟨j,hj⟩⟩ := by
        unfold DrawingPassages.orderedInner
        congr 1
        apply Subtype.ext
        apply Fin.ext
        change j.val-1+1=j.val
        omega
      rw [heq]
      exact hx

end Zarankiewicz.PolygonalExterior

end

end OAI
