import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList
import OAI.Geometry.HyperbolicGroups.BoundaryLift

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S : Type*} [DecidableEq D] [DecidableEq S]

/-- An indexed face map pulls back a complete target polygon to exactly one
source face, without any injectivity assumption on target letter labels. -/
theorem IndexedFaceMap.pullback_boundary {f : Perm D} {t : Perm S} {j : D → S}
    (h : IndexedFaceMap f t j) (a : D) {ys : List S}
    (ht : IsBoundary t ys) (ha : j a ∈ ys) :
    ∃ xs : List D, IsBoundary f xs ∧ a ∈ xs ∧ xs.map j = ys := by
  let p : D → Prop := fun x => f.SameCycle a x
  have hp : ∀ x, p (f x) ↔ p x := by
    intro x
    exact ⟨fun h => h.trans SameCycle.rfl.apply_right.symm,
      fun h => h.trans SameCycle.rfl.apply_right⟩
  let q := f.subtypePerm hp
  let jj : {x // p x} → S := fun x => j x.val
  have hj : Function.Injective jj := by
    intro x y he
    apply Subtype.ext
    exact h.injective (x.property.symm.trans y.property) he
  obtain ⟨zs,hzs,hzm⟩ := ht.pullback_surviving jj hj (by
    intro s hs
    obtain ⟨x,hx,he⟩ := h.orbit_surjective a (ht.sameCycle ha hs)
    exact ⟨⟨x,hx⟩,he⟩) (q := q) (by intro x _; exact h.commute x.val)
  refine ⟨zs.map Subtype.val,?_,?_,?_⟩
  · exact hzs.map Subtype.val Subtype.val_injective (fun _ => rfl)
  · have hm : j a ∈ zs.map jj := hzm.symm ▸ ha
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    have hxa : x.val = a := h.injective x.property.symm he
    exact hxa ▸ List.mem_map_of_mem (f := Subtype.val) hx
  · simpa only [List.map_map,jj,Function.comp_def] using hzm

end HyperbolicObstruction.PictureSwitch
end

end OAI
