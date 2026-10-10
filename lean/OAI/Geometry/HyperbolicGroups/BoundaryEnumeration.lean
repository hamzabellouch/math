import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

/-- Every finite face orbit has a literal nonempty boundary enumeration,
including monogons (which Perm.toList alone omits). -/
theorem exists_boundary (p : Perm D) (a : D) :
    ∃ xs, IsBoundary p xs ∧ a ∈ xs := by
  by_cases ha : p a = a
  · refine ⟨[a],⟨by simp,?_⟩,by simp⟩
    intro x hx
    have he : x = a := by simpa only [List.mem_singleton] using hx
    subst x
    simpa only [List.formPerm_singleton,one_apply] using ha
  · have has : a ∈ p.support := mem_support.mpr ha
    refine ⟨p.toList a,⟨p.nodup_toList a,?_⟩,mem_toList_iff.mpr ⟨SameCycle.rfl,has⟩⟩
    intro x hx
    rw [formPerm_toList]
    rw [cycleOf_apply,ite_eq_left (mem_toList_iff.mp hx).1]

lemma IsBoundary.length_eq_card {p : Perm D} {xs : List D} (h : IsBoundary p xs)
    {a : D} (ha : a ∈ xs) :
    xs.length = Fintype.card {x : D // p.SameCycle a x} := by
  rw [Fintype.card_of_subtype xs.toFinset (by
    intro x
    rw [List.mem_toFinset]
    exact ⟨h.sameCycle ha,h.mem_of_sameCycle ha⟩),List.toFinset_card_of_nodup h.nodup]

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
