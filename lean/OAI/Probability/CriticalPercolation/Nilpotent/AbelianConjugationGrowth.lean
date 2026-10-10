import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.ConjugationMatrixGrowth
import OAI.Probability.CriticalPercolation.LinearGroups.MatrixPeriodicDirection

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix IsMulCommutative

namespace CriticalPercolation.SparseGrowth

variable {B : Type*} [CommGroup B]

lemma periodic_lift_of_torsion_coset (f : B ≃* B) (x : B)
    (hx : ¬IsOfFinOrder x) (hfix : f x * x⁻¹ ∈ CommGroup.torsion B) :
    ∃ y : B, ¬IsOfFinOrder y ∧ f y=y := by
  obtain ⟨k,hk,he⟩ := (CommGroup.mem_torsion _).mp hfix |>.exists_pow_eq_one
  refine ⟨x^k,fun hy => hx (hy.of_pow (Nat.ne_of_gt hk)),?_⟩
  rw [map_pow]
  rw [mul_pow,inv_pow,mul_inv_eq_one] at he
  exact he

lemma infinite_fg_commgroup_quotient_torsion_nontrivial [Group.FG B] [Infinite B] :
    Nontrivial (B ⧸ CommGroup.torsion B) := by
  by_contra h
  have hs : Subsingleton (B ⧸ CommGroup.torsion B) := not_nontrivial_iff_subsingleton.mp h
  have ht : IsMulTorsion B := by
    intro x
    exact (QuotientGroup.eq_one_iff (N := CommGroup.torsion B) x).mp (Subsingleton.elim _ _)
  let _ := CommGroup.finite_of_fg_isMulTorsion B ht
  exact not_finite B

variable {A : Type*} [Group A] [DecidableEq A]

theorem HasPolynomialDegree.abelian_normal_periodic_direction {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    [IsMulCommutative H] [Group.FG H] [Infinite H] (a : A) :
    ∃ m : ℕ, 0 < m ∧ ∃ x : H, ¬IsOfFinOrder x ∧ (MulAut.conjNormal (a^m)) x=x := by
  let T := CommGroup.torsion H
  let Q := H ⧸ T
  let _ : Nontrivial Q := infinite_fg_commgroup_quotient_torsion_nontrivial
  let V := Additive Q
  let _ : Module.Finite ℤ V := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : Module.Free ℤ V := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ V
  let b := Module.Free.chooseBasis ℤ V
  let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ V
  let _ : Nonempty ι := b.index_nonempty
  let e := b.equivFun
  let c : Q ≃* Multiplicative (ι → ℤ) :=
    { toFun := fun q => Multiplicative.ofAdd (e (Additive.ofMul q))
      invFun := fun v => Additive.toMul (e.symm (Multiplicative.toAdd v))
      left_inv := by intro q; exact congrArg Additive.toMul (e.symm_apply_apply _)
      right_inv := by intro v; exact congrArg Multiplicative.ofAdd (e.apply_symm_apply _)
      map_mul' := by intro x y; exact congrArg Multiplicative.ofAdd (e.map_add _ _) }
  let f := MulAut.conjNormal a (H := H)
  let fQ := QuotientGroup.congr T T f f.map_torsion
  let fV : V ≃ₗ[ℤ] V := fQ.toAdditive.toIntLinearEquiv
  let M := LinearMap.toMatrix b b fV.toLinearMap
  have hfunit : IsUnit fV.toLinearMap := by
    refine ⟨⟨fV.toLinearMap,fV.symm.toLinearMap,?_,?_⟩,rfl⟩ <;> ext x <;> simp
  have hMunit : IsUnit M := hfunit.map (LinearMap.toMatrixAlgEquiv b)
  let p := c.toMonoidHom.comp (QuotientGroup.mk' T)
  have hp : Surjective p := c.surjective.comp (QuotientGroup.mk'_surjective T)
  have hM : ∀ x : H, Multiplicative.toAdd (p (f x))=M.mulVec (Multiplicative.toAdd (p x)) := by
    intro x
    change e (Additive.ofMul ((QuotientGroup.mk' T) (f x))) =
      M.mulVec (e (Additive.ofMul ((QuotientGroup.mk' T) x)))
    have he := (LinearMap.toMatrix_mulVec_repr b b fV.toLinearMap
      (Additive.ofMul ((QuotientGroup.mk' T) x))).symm
    simpa [←Module.Basis.equivFun_apply, fV, fQ, e, M, MulEquiv.toAdditive] using he
  have hroots := hg.conjugationMatrix_roots_norm_le_one H a p hp M hM
  obtain ⟨m,hm,v,hv,hMv⟩ := intMatrix_exists_periodic_vector M hMunit hroots
  let q := c.symm (Multiplicative.ofAdd v)
  obtain ⟨x,hxq⟩ := QuotientGroup.mk'_surjective T q
  have hqne : q≠1 := by
    intro h
    apply hv
    have hh := congrArg c h
    simpa [q] using hh
  have hx : ¬IsOfFinOrder x := by
    intro hx
    have hqfin : IsOfFinOrder q := hxq ▸ (QuotientGroup.mk' T).isOfFinOrder hx
    exact isMulTorsionFree_iff_not_isOfFinOrder.mp (inferInstance : IsMulTorsionFree Q) hqne hqfin
  have hMp (n : ℕ) (y : H) :
      Multiplicative.toAdd (p ((MulAut.conjNormal (a^n)) y))=
        (M^n).mulVec (Multiplicative.toAdd (p y)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',map_mul,MulAut.mul_apply,hM,ih,Matrix.mulVec_mulVec,←pow_succ']
  have hpx : Multiplicative.toAdd (p x)=v := by
    change Multiplicative.toAdd (c ((QuotientGroup.mk' T) x))=v
    rw [hxq]
    exact congrArg Multiplicative.toAdd (c.apply_symm_apply _)
  have hT : (MulAut.conjNormal (a^m)) x*x⁻¹ ∈ T := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' T) (_*_)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
    apply c.injective
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (p ((MulAut.conjNormal (a^m)) x))=
      Multiplicative.toAdd (p x)
    rw [hMp,hpx,hMv]
  obtain ⟨y,hy,hyfix⟩ := periodic_lift_of_torsion_coset (MulAut.conjNormal (a^m)) x hx hT
  exact ⟨m,hm,y,hy,hyfix⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
