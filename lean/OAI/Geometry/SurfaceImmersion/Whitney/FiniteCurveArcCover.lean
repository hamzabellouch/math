import OAI.Geometry.SurfaceImmersion.Whitney.HalfLineCompactArc

namespace OAI

/-! Compactness reduces the actual local line and half-line charts to a
finite cover by compact embedded arcs with open interiors. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem finite_curve_arc_cover
    (hchart : ∀ x : X,
      (∃ c : OpenPartialHomeomorph X ℝ, x ∈ c.source) ∨
      (∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)), x ∈ c.source ∧ c x = ⟨0,by simp⟩)) :
    ∃ (A : X → CompactCurveArc X) (V : X → Set X) (s : Finset X),
      (∀ x, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ range (A x).map) ∧
      (univ : Set X) ⊆ ⋃ x ∈ s, V x := by
  classical
  have hex (x : X) : ∃ (A : CompactCurveArc X) (V : Set X),
      IsOpen V ∧ x ∈ V ∧ V ⊆ range A.map := by
    rcases hchart x with ⟨c,hc⟩ | ⟨c,hc,hc0⟩
    · exact line_chart_compact_arc c hc
    · exact half_line_compact_arc c hc hc0
  choose A V hV hxV hsub using hex
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x,hxV x⟩)
  exact ⟨A,V,s,fun x => ⟨hV x,hxV x,hsub x⟩,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
