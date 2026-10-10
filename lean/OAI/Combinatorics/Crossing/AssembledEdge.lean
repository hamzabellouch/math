import OAI.Combinatorics.Crossing.MiddleSpokeMeeting

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

def startSpoke (C : DrawingPassages D) (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Path (v (.inl e.1)) (C.arcStart (C.firstArc e)) := Path.segment _ _

def endSpoke (C : DrawingPassages D) (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Path (C.arcEnd (C.lastArc e)) (v (.inr e.2)) := (Path.segment _ _).symm

def assembledEdge (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (e : BipartiteEdge m n) : Path (v (.inl e.1)) (v (.inr e.2)) :=
  ((startSpoke C v e).trans (E.anchoredMiddle e)).trans (endSpoke C v e)

theorem startSpoke_injective (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (startSpoke C v e) := C.vertex_spoke_injective v hv _ (C.startPortAt e)

theorem endSpoke_range (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    Set.range (endSpoke C v e)=Set.range (Path.segment (v (.inr e.2)) (C.portPoint (C.endPortAt e).val)) := by
  exact Path.symm_range _

theorem endSpoke_injective (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (endSpoke C v e) := by
  intro s t he
  have hh := C.vertex_spoke_injective v hv _ (C.endPortAt e) he
  have hval := congrArg Subtype.val hh
  apply Subtype.ext
  change 1-s.val=1-t.val at hval
  linarith

theorem assembledEdge_injective (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : BipartiteEdge m n) :
    Function.Injective (E.assembledEdge v e) := by
  have hfirst : Function.Injective ((startSpoke C v e).trans (E.anchoredMiddle e)) := by
    apply path_trans_injective _ _ (startSpoke_injective v hv e) (E.anchoredMiddle_injective e)
    intro x hx hy
    exact E.middle_spoke_meeting v hv e _ (C.startPortAt e) x hy hx
  apply path_trans_injective _ _ hfirst (endSpoke_injective v hv e)
  intro x hx hy
  rw [Path.trans_range] at hx
  rw [endSpoke_range] at hy
  rcases hx with hx | hx
  · have hd := C.vertex_spokes_disjoint_of_vertices_ne v hv (.inl e.1) (.inr e.2)
      (by simp) (C.startPortAt e) (C.endPortAt e)
    exact False.elim (Set.disjoint_left.mp hd hx hy)
  · exact E.middle_spoke_meeting v hv e _ (C.endPortAt e) x hx hy

theorem assembledEdge_range_iff (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane)
    (e : BipartiteEdge m n) (x : Plane) :
    x ∈ Set.range (E.assembledEdge v e) ↔
      (x ∈ Set.range (startSpoke C v e) ∨
        (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
        (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p))) ∨
      x ∈ Set.range (endSpoke C v e) := by
  simp only [assembledEdge,Path.trans_range,Set.mem_union,anchoredMiddle_range,E.middlePath_range_iff]

end Zarankiewicz.PolygonalExterior

end

end OAI
