import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryDualAction

variable {A : Type*} [CStarAlgebra A]

lemma weak_ext {f g : WeakDual ℂ A} (h : ∀ a,f a=g a) : f=g :=
  WeakDual.toStrongDual.injective (ContinuousLinearMap.ext h)

def act (u : unitary A) (f : WeakDual ℂ A) : WeakDual ℂ A :=
  StrongDual.toWeakDual (f.toStrongDual.comp (ContinuousLinearMap.mulLeftRight ℂ A (star (u:A)) (u:A)))

@[simp] lemma act_apply (u : unitary A) (f : WeakDual ℂ A) (a : A) :
    act u f a=f (star (u:A)*a*(u:A)) := rfl

instance action : MulAction (unitary A) (WeakDual ℂ A) where
  smul := act
  one_smul f := by apply weak_ext; intro a; change f (star (1:A)*a*1)=f a; simp
  mul_smul u v f := by
    apply weak_ext
    intro a
    change f (star ((u:A)*(v:A))*a*((u:A)*(v:A)))=
      f (star (v:A)*(star (u:A)*a*(u:A))*(v:A))
    simp only [star_mul,mul_assoc]

@[simp] lemma smul_apply (u : unitary A) (f : WeakDual ℂ A) (a : A) :
    (u • f) a=f (star (u:A)*a*(u:A)) := rfl

instance continuous_action : ContinuousConstSMul (unitary A) (WeakDual ℂ A) where
  continuous_const_smul u := WeakDual.continuous_of_continuous_eval
    (fun a => WeakDual.eval_continuous (star (u:A)*a*(u:A)))

lemma conjugate_norm (u : unitary A) (a : A) :
    ‖star (u:A)*a*(u:A)‖=‖a‖ := by
  rw [CStarRing.norm_mul_coe_unitary]
  exact CStarRing.norm_coe_unitary_mul (star u) a

lemma act_norm_le (u : unitary A) (f : WeakDual ℂ A) :
    ‖(u • f).toStrongDual‖≤‖f.toStrongDual‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  change ‖f.toStrongDual (star (u:A)*a*(u:A))‖≤‖f.toStrongDual‖*‖a‖
  simpa only [conjugate_norm] using f.toStrongDual.le_opNorm (star (u:A)*a*(u:A))

lemma act_norm (u : unitary A) (f : WeakDual ℂ A) :
    ‖(u • f).toStrongDual‖=‖f.toStrongDual‖ := by
  apply (act_norm_le u f).antisymm
  have h := act_norm_le u⁻¹ (u • f)
  simpa only [inv_smul_smul] using h

lemma act_sub (u : unitary A) (f g : WeakDual ℂ A) : u • (f-g)=u • f-u • g := by
  apply weak_ext
  intro a
  rfl

lemma act_dist (u : unitary A) (f g : WeakDual ℂ A) :
    dist (u • f).toStrongDual (u • g).toStrongDual=dist f.toStrongDual g.toStrongDual := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : (u • f).toStrongDual-(u • g).toStrongDual=(u • (f-g)).toStrongDual := by
    rw [act_sub,map_sub]
  rw [he,act_norm,map_sub]

lemma act_linear (u : unitary A) :
    ∃ L : WeakDual ℂ A →ₗ[ℝ] WeakDual ℂ A,∀ f,L f=u • f := by
  exact ⟨{ toFun := fun f => u • f
           map_add' := fun f g => by apply weak_ext; intro a; rfl
           map_smul' := fun c f => by apply weak_ext; intro a; rfl },fun _ => rfl⟩

theorem trace_of_fixed (f : WeakDual ℂ A) (hf : ∀ u : unitary A,u • f=f) :
    ∀ a b : A,f (a*b)=f (b*a) := by
  intro a b
  let L : A →ₗ[ℂ] ℂ := f.toStrongDual.toLinearMap.comp (LinearMap.mulRight ℂ b)
  let R : A →ₗ[ℂ] ℂ := f.toStrongDual.toLinearMap.comp (LinearMap.mulLeft ℂ b)
  have hEq : L=R := by
    apply LinearMap.ext_on (CStarAlgebra.span_unitary A)
    intro v hv
    let u : unitary A := ⟨v,hv⟩
    have h := congrArg (fun g : WeakDual ℂ A => g (v*b)) (hf u)
    change f (star v*(v*b)*v)=f (v*b) at h
    have he : star v*(v*b)*v=b*v := by
      rw [←mul_assoc (star v) v b,hv.1,one_mul]
    rw [he] at h
    exact h.symm
  exact congrArg (fun T : A →ₗ[ℂ] ℂ => T a) hEq

end Kadison.UnitaryDualAction

end

end
end

end OAI
