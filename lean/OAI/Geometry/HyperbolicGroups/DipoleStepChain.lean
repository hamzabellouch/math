import Mathlib
import OAI.Geometry.HyperbolicGroups.DipoleRemove

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I A : Type*} [Fintype D] [Fintype I]
  [AddCommMonoid A]
namespace PictureMap

/-- Corner-wise version of signed dipole-chain preservation. It allows the
coefficient of a frozen face to be carried at one indexed corner and the
coefficients of top elementary cone triangles at individual macro steps. -/
lemma sum_not_inDipole {f : Perm D} {q : Perm I} {a b : I → D}
    (hF : OppositeFaces f q a b) (w : D → A) (hw : ∀ i, w (a i) + w (b i) = 0) :
    ∑ x : {x : D // ¬ InDipole a b x}, w x.val = ∑ x : D, w x := by
  classical
  let j : I ⊕ I → {x : D // InDipole a b x} :=
    fun x => match x with
      | .inl i => ⟨a i,Or.inl ⟨i,rfl⟩⟩
      | .inr i => ⟨b i,Or.inr ⟨i,rfl⟩⟩
  have hj : Function.Bijective j := by
    constructor
    · intro x y h
      have hh := congrArg Subtype.val h
      cases x with
      | inl i => cases y with
        | inl k => exact congrArg Sum.inl (hF.a_inj hh)
        | inr k => exact False.elim (hF.disjoint i k hh)
      | inr i => cases y with
        | inl k => exact False.elim (hF.disjoint k i hh.symm)
        | inr k => exact congrArg Sum.inr (hF.b_inj hh)
    · intro x
      rcases x.property with ⟨i,hi⟩ | ⟨i,hi⟩
      · exact ⟨.inl i,Subtype.ext hi⟩
      · exact ⟨.inr i,Subtype.ext hi⟩
  have hz : ∑ x : {x : D // InDipole a b x}, w x.val = 0 := by
    rw [← Equiv.sum_comp (Equiv.ofBijective j hj)]
    simp only [Equiv.ofBijective_apply,Fintype.sum_sum_type,j]
    rw [← Finset.sum_add_distrib]
    simp only [hw,Finset.sum_const_zero]
  have hh := Fintype.sum_subtype_add_sum_subtype (InDipole a b) w
  rw [hz,zero_add] at hh
  exact hh

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
