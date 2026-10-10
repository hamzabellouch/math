import OAI.Combinatorics.Crossing.PolygonalExterior

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem chord_parameter_endpoint (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) : t=0 ∨ t=1 := by
  by_cases ht0 : t=0
  · exact Or.inl ht0
  by_cases ht1 : t=1
  · exact Or.inr ht1
  have h := C.crossingChord_interior_in_disk p t
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have hx := E.outside_open_disks i s (C.innerMark p)
  rw [he] at hx
  exact False.elim (h.not_ge hx)

theorem exterior_chord_meeting_parameters (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) :
    (i=C.incomingArc p ∧ s=1 ∧ t=0) ∨ (i=C.outgoingArc p ∧ s=0 ∧ t=1) := by
  have hs := E.parameter_endpoint_of_mem_disk i s (C.innerMark p) (by
    rw [he]
    exact C.crossingChord_range_subset_disk p ⟨t,rfl⟩)
  have ht := E.chord_parameter_endpoint i p s t he
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp only [Path.source] at he
    have hp : (i,false)=C.incomingPort p := C.portPoint_injective he
    have hh : false=true := congrArg Prod.snd hp
    cases hh
  · simp only [Path.source,Path.target] at he
    have hp : (i,false)=C.outgoingPort p := C.portPoint_injective he
    exact Or.inr ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.source,Path.target] at he
    have hp : (i,true)=C.incomingPort p := C.portPoint_injective he
    exact Or.inl ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.target] at he
    have hp : (i,true)=C.outgoingPort p := C.portPoint_injective he
    have hh : true=false := congrArg Prod.snd hp
    cases hh

end Zarankiewicz.PolygonalExterior

end

end OAI
