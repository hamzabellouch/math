import Mathlib
import OAI.Probability.CriticalPercolation.Nilpotent.FiniteCyclicConstruction
import OAI.Probability.CriticalPercolation.Criticality.SubgroupFiniteIndexExtension
import OAI.Probability.CriticalPercolation.Nilpotent.CyclicSubgroupIndex

namespace OAI

universe groupUniverse

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

theorem FiniteCyclicConstruction.subgroup {G : Type groupUniverse} [Group G] {n : ℕ}
    (hG : FiniteCyclicConstruction G n) :
    ∀ J : Subgroup G, ∃ m≤n, FiniteCyclicConstruction J m ∧ (m=n → J.FiniteIndex) := by
  induction hG with
  | @finite G _ _ =>
    intro J
    exact ⟨0,le_rfl,.finite _,fun _ => inferInstance⟩
  | @cyclic G _ e =>
    intro J
    cases finite_or_infinite J with
    | inl h =>
      let _ := h
      exact ⟨0,by omega,.finite _,by omega⟩
    | inr h =>
      let _ := h
      let _ : IsCyclic G := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact ⟨1,le_rfl,.cyclic _ (intCyclicMulEquiv.symm),
        fun _ => cyclic_infinite_subgroup_finiteIndex e J⟩
  | @extension G Q _ _ f hf n m hker hquot ihker ihquot =>
    intro J
    obtain ⟨k,hk,hK,hki⟩ := ihker (J.subgroupOf f.ker)
    obtain ⟨l,hl,hL,hli⟩ := ihquot (J.map f)
    let g : J →* J.map f := {
      toFun := fun j => ⟨f j.val,⟨j.val,j.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' := by intros; apply Subtype.ext; exact f.map_mul _ _ }
    have hg : Surjective g := by
      rintro ⟨q,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    let e : g.ker ≃* J.subgroupOf f.ker := {
      toFun := fun a => ⟨⟨a.val.val,congrArg Subtype.val a.property⟩,a.val.property⟩
      invFun := fun a => ⟨⟨a.val.val,a.property⟩,Subtype.ext a.val.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl
      map_mul' := by intros; rfl }
    refine ⟨k+l,by omega,FiniteCyclicConstruction.extension g hg (hK.of_equiv e) hL,?_⟩
    intro he
    let _ := hki (by omega)
    let _ := hli (by omega)
    exact subgroup_finiteIndex_of_image_and_kernel f hf J

end CriticalPercolation
end
end
end

end OAI
