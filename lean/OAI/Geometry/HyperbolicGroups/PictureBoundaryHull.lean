import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.TreeHull
import OAI.Geometry.HyperbolicGroups.SubpairingDarts
import OAI.Geometry.HyperbolicGroups.SubpairingTree
import OAI.Geometry.HyperbolicGroups.PictureBoundaryParity

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

/-- The topological separation mechanism behind the tree--cotree separator.
A face coloring can change across tree edges only inside the root-path hull
of its non-tree changes. Proof: literal vertex-rotation conservation gives
two distinct boundary Dart copies at every unprotected boundary vertex;
exact tree-copy uniqueness turns them into two distinct tree neighbors,
contradicting a furthest-vertex argument. -/
theorem face_color_boundary_in_hull (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1)
    (root : M.GraphVertex) (S : Set M.GraphVertex)
    (hS : RootClosed (M.subpairingGraph q (M.subpairing_sq q hq)) root S)
    {C : Type*} (color : D → C) (hface : ∀ x, color (M.face x) = color x)
    (hother : ∀ x, q x = x → color (M.edge x) ≠ color x → M.vertexClass x ∈ S) :
    ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S := by
  let G := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : G.IsTree := M.subpairing_isTree hG q hq hspan hboundary
  let B : M.GraphVertex → Prop := fun v => ∃ x, M.vertexClass x = v ∧ color (M.edge x) ≠ color x
  have hb : ∀ v, B v → v ∈ S := by
    apply tree_boundary_in_hull hT root S hS B
    intro v hv hvS
    obtain ⟨x,hxv,hxc⟩ := hv
    have hxq : q x ≠ x := fun he => hvS (hxv ▸ hother x he hxc)
    obtain ⟨y,hyx,hyv,hyc⟩ := M.boundary_dart_not_unique color hface x hxc
    have hyq : q y ≠ y := fun he => hvS ((hyv.trans hxv) ▸ hother y he hyc)
    have hxe : q x = M.edge x := (hq x).resolve_left hxq
    have hye : q y = M.edge y := (hq y).resolve_left hyq
    refine ⟨M.vertexClass (M.edge x),M.vertexClass (M.edge y),?_,?_,?_,?_,?_⟩
    · intro he
      exact hyx (M.tree_retained_dart_unique q hq hG hspan hboundary x y hxq hyq hyv.symm he).symm
    · refine ⟨?_,x,hxv,?_⟩
      · rw [← hxv]
        exact M.tree_retained_loopless q hq hG hspan hboundary x hxq
      · rw [hxe]
    · refine ⟨?_,y,hyv.trans hxv,?_⟩
      · rw [← hxv,← hyv]
        exact M.tree_retained_loopless q hq hG hspan hboundary y hyq
      · rw [hye]
    · refine ⟨M.edge x,rfl,?_⟩
      rw [M.edge_edge]
      exact hxc.symm
    · refine ⟨M.edge y,rfl,?_⟩
      rw [M.edge_edge]
      exact hyc.symm
  intro x hx
  exact hb _ ⟨x,rfl,hx⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
