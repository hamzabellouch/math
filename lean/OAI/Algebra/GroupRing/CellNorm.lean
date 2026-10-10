import Mathlib
import OAI.Algebra.GroupRing.CellModule
import OAI.Algebra.GroupRing.FreeActionNorm

namespace OAI



section
namespace TorsionFreeZeroDivisors.CellNorm
open scoped Classical BigOperators
open CellModule
noncomputable section
variable {H G I : Type} [CommGroup H] [Group G] [Fintype H]
  (φ : H→*G) (hφ : Function.Injective φ)
def norm (x : CellModule.Module G I) : CellModule.Module G I := ∑h:H,translate (φ h) x
lemma norm_add (x y : CellModule.Module G I) : norm φ (x+y)=norm φ x+norm φ y := by
  simp only [norm,map_add,Finset.sum_add_distrib]
lemma norm_sub (x y : CellModule.Module G I) : norm φ (x-y)=norm φ x-norm φ y := by
  simp only [norm,map_sub,Finset.sum_sub_distrib]
lemma equivariance (J : Type) (f : CellModule.Module G I→+CellModule.Module G J)
    (hf : ∀g x,f (translate g x)=translate g (f x)) (x : CellModule.Module G I) :
    f (norm φ x)=norm φ (f x) := by
  simp only [norm,map_sum,hf]
@[instance_reducible] def moduleAction : MulAction H (G×I) where
  smul h p := (φ h*p.1,p.2)
  one_smul p := by change (φ 1*p.1,p.2)=p; simp
  mul_smul h k p := by change (φ (h*k)*p.1,p.2)=(φ h*(φ k*p.1),p.2); rw [map_mul,mul_assoc]
include hφ in
lemma invariant_norm (g : H) (hg : ∀h,h∈Subgroup.zpowers g) (x : CellModule.Module G I)
    (hx : translate (φ g) x=x) : ∃y,norm φ y=x := by
  let : MulAction H (G×I) := moduleAction φ
  let : IsCancelSMul H (G×I) := {
    right_cancel' h k p he := hφ (mul_right_cancel (congrArg Prod.fst he)) }
  have hact (h : H) (y : CellModule.Module G I) : FreeActionNorm.act h y=translate (φ h) y := by
    ext p
    change y (φ h⁻¹*p.1,p.2)=y ((φ h)⁻¹*p.1,p.2)
    rw [map_inv]
  obtain ⟨y,hy⟩ := FreeActionNorm.invariant_norm g hg x ((hact g x).trans hx)
  exact ⟨y,by simpa only [FreeActionNorm.norm,hact,norm] using hy⟩
include hφ in
lemma kernel_norm (g : H) (hg : ∀h,h∈Subgroup.zpowers g) (x : CellModule.Module G I)
    (hx : norm φ x=0) : ∃y,translate (φ g) y-y=x := by
  let : MulAction H (G×I) := moduleAction φ
  let : IsCancelSMul H (G×I) := {
    right_cancel' h k p he := hφ (mul_right_cancel (congrArg Prod.fst he)) }
  have hact (h : H) (y : CellModule.Module G I) : FreeActionNorm.act h y=translate (φ h) y := by
    ext p
    change y (φ h⁻¹*p.1,p.2)=y ((φ h)⁻¹*p.1,p.2)
    rw [map_inv]
  have hn : FreeActionNorm.norm (H:=H) x=0 := by simpa only [FreeActionNorm.norm,hact,norm] using hx
  obtain ⟨y,hy⟩ := FreeActionNorm.kernel_norm g hg x hn
  exact ⟨y,by rw [hact] at hy;exact hy⟩

def augmentation : CellModule.Module G I→+ℤ := Finsupp.liftAddHom (fun _=>AddMonoidHom.id ℤ)
omit [Group G] in
@[simp] lemma augmentation_single (p : G×I) (z : ℤ) : augmentation (Finsupp.single p z)=z := by simp [augmentation]
lemma augmentation_translate (g : G) (x : CellModule.Module G I) : augmentation (translate g x)=augmentation x := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb]
  | single p z=>simp only [translate_single,augmentation_single]
lemma augmentation_norm (x : CellModule.Module G I) : augmentation (norm φ x)=(Fintype.card H:ℤ)*augmentation x := by
  simp only [norm,map_sum,augmentation_translate,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
lemma augmentation_boundary {A : Type} (q : FreeGroup A→*G) (x : CellModule.Module G A) :
    augmentation (boundary q x)=0 := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb,add_zero]
  | single p z=>simp only [boundary_single,map_sub,augmentation_single,sub_self]
include hφ in
lemma invariant_augmentation (g : H) (hg : ∀h,h∈Subgroup.zpowers g) (x : CellModule.Module G I)
    (hx : translate (φ g) x=x) : (Fintype.card H:ℤ)∣augmentation x := by
  obtain ⟨y,hy⟩ := invariant_norm φ hφ g hg x hx
  exact ⟨augmentation y,by rw [←hy,augmentation_norm]⟩
end
end TorsionFreeZeroDivisors.CellNorm

end



end OAI
