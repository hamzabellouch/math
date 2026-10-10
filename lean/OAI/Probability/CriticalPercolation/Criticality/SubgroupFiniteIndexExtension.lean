import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation

theorem subgroup_finiteIndex_of_image_and_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Surjective f) (J : Subgroup G)
    [(J.map f).FiniteIndex] [(J.subgroupOf f.ker).FiniteIndex] : J.FiniteIndex := by
  let S := J ⊔ f.ker
  have hS : S.FiniteIndex := by
    constructor
    have hn := (inferInstance : (J.map f).FiniteIndex).index_ne_zero
    rw [Subgroup.index_map,f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one] at hn
    exact hn
  let _ := hS
  let inc : f.ker →* S := {
    toFun := fun x => ⟨x.val,(le_sup_right : f.ker≤J⊔f.ker) x.property⟩
    map_one' := rfl
    map_mul' := by intros; rfl }
  let F : (f.ker ⧸ J.subgroupOf f.ker) → (S ⧸ J.subgroupOf S) :=
    Quotient.map inc (by
      intro a b hab
      apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
      exact (QuotientGroup.leftRel_apply (s := J.subgroupOf f.ker)).mp hab)
  have hF : Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x.val∈(f.ker : Set G)*(J : Set G) := by
      rw [←Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    refine ⟨QuotientGroup.mk ⟨a,ha⟩,?_⟩
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
    change a⁻¹*x.val∈J
    rw [←he,inv_mul_cancel_left]
    exact hb
  let _ : Finite (S ⧸ J.subgroupOf S) := Finite.of_surjective F hF
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  exact Finite.of_equiv _ (Subgroup.quotientEquivProdOfLE (le_sup_left : J≤S)).symm

end CriticalPercolation
end
end
end

end OAI
