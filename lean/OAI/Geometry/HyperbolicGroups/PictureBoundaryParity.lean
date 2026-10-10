import Mathlib
import OAI.Geometry.HyperbolicGroups.PermErase
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

/-- A cyclic word cannot have just one change of color. The colors need not
be Boolean; the proof counts the occurrences of the color at the exceptional
position. This is the literal rotation-system boundary conservation law. -/
lemma perm_transition_not_unique {C : Type*} (p : Perm D) (color : D → C) (x : D)
    (hx : color (p x) ≠ color x) :
    ∃ y : D, y ≠ x ∧ p.SameCycle x y ∧ color (p y) ≠ color y := by
  classical
  by_contra h
  push Not at h
  let V := {y : D // p.SameCycle x y}
  let z : V := ⟨x,SameCycle.rfl⟩
  let r : Perm V := p.subtypePerm (fun y => sameCycle_apply_right)
  let f : V → ℕ := fun y => if color y.val = color x then 1 else 0
  have hz : f z = 1 := by simp [f,z]
  have hrz : f (r z) = 0 := by
    change (if color (p x) = color x then 1 else 0) = 0
    simp only [ite_eq_right hx]
  have hrest : ∀ y ∈ (Finset.univ : Finset V).erase z, f (r y) = f y := by
    intro y hy
    have hne : y.val ≠ x := fun he => (Finset.mem_erase.mp hy).1 (Subtype.ext he)
    have hc := h y.val hne y.property
    change (if color (p y.val) = color x then 1 else 0) =
      (if color y.val = color x then 1 else 0)
    rw [hc]
  have hs := Equiv.sum_comp r f
  have hs₁ := Finset.sum_erase_add (Finset.univ : Finset V) (f ∘ r) (Finset.mem_univ z)
  have hs₂ := Finset.sum_erase_add (Finset.univ : Finset V) f (Finset.mem_univ z)
  have he : ∑ y ∈ (Finset.univ : Finset V).erase z, (f ∘ r) y =
      ∑ y ∈ (Finset.univ : Finset V).erase z, f y := by
    apply Finset.sum_congr rfl
    exact hrest
  change (∑ y ∈ (Finset.univ : Finset V).erase z, (f ∘ r) y) + f (r z) = _ at hs₁
  rw [he,hrz] at hs₁
  rw [hz] at hs₂
  change (∑ y : V, f (r y)) = ∑ y : V, f y at hs
  simp only [Function.comp_apply] at hs₁
  omega

namespace PictureMap
variable (M : PictureMap D)

/-- If a coloring is constant around faces, every vertex incident to a
color-boundary edge has at least TWO distinct incident boundary darts.
Parallel edges and loops are retained; there is no simple-graph assumption. -/
theorem boundary_dart_not_unique {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (x : D)
    (hx : color (M.edge x) ≠ color x) :
    ∃ y : D, y ≠ x ∧ M.vertexClass y = M.vertexClass x ∧
      color (M.edge y) ≠ color y := by
  have hv : ∀ y, color (M.vertex y) = color (M.edge y) := by
    intro y
    exact hface (M.edge y)
  obtain ⟨y,hne,hcycle,hy⟩ := perm_transition_not_unique M.vertex color x (by rwa [hv])
  refine ⟨y,hne,(M.vertexClass_eq_iff y x).mpr hcycle.symm,?_⟩
  rwa [hv] at hy

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
