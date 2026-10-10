import OAI.Geometry.SurfaceImmersion.Whitney.HalfLineCompactArc
import OAI.Geometry.SurfaceImmersion.Geometry.SubarcClosure

namespace OAI

/-! A boundary chart admits a connected punctured neighborhood avoiding
all other vertices of a prescribed finite set. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem half_line_punctured_neighborhood
    (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩)
    (V : Set X) (hV : V.Finite) :
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ IsConnected (W \ {p}) ∧
      W \ {p} ⊆ Vᶜ ∧ p ∈ closure (W \ {p}) := by
  have hD : IsClosed (V \ {p}) := (hV.subset sdiff_subset).isClosed
  let U : Set X := (V \ {p})ᶜ
  have hU : IsOpen U := hD.isOpen_compl
  have hpU : p ∈ U := by
    rintro ⟨_,hn⟩
    exact hn rfl
  let e := c.restrOpen U hU
  have hpe : p ∈ e.source := ⟨hp,hpU⟩
  have he0 : e p = ⟨0,by simp⟩ := hzero
  obtain ⟨A,W,hW,hpW,_,hleft,hWS,hWe⟩ := half_line_compact_arc_data e hpe he0
  refine ⟨W,hW,hpW,?_,?_,?_⟩
  · rw [hWS]
    exact A.subarc_connected le_rfl le_rfl A.ordered
  · rintro x ⟨hxW,hxp⟩ hxV
    exact (hWe hxW).2 ⟨hxV,hxp⟩
  · rw [hWS,A.subarc_closure le_rfl le_rfl A.ordered]
    exact ⟨⟨A.left,le_rfl,A.ordered.le⟩,⟨le_rfl,A.ordered.le⟩,hleft⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
