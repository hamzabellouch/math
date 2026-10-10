import Mathlib
import OAI.Analysis.WeakInfiniteness.UnitaryIntertwining

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u

variable {B : Type u} [NonUnitalCStarAlgebra B]

lemma norm_unitizationInnerFun_sub (u : unitary (Unitization ℂ B)) (b : B) :
    ‖unitizationInnerFun u b-b‖=‖(u.val.snd)*b-b*(u.val.snd)‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ) (unitizationInnerFun u b-b),
    Unitization.inr_sub,inr_unitizationInnerFun,Unitary.conjStarAlgAut_apply]
  have he : u.val*(b:Unitization ℂ B)*star u.val-(b:Unitization ℂ B)=
      (u.val*(b:Unitization ℂ B)-(b:Unitization ℂ B)*u.val)*star u.val := by
    rw [sub_mul,mul_assoc (b:Unitization ℂ B),Unitary.mul_star_self_of_mem u.property, mul_one]
  rw [he]
  have hu : star u.val=(star u).val := rfl
  rw [hu,CStarRing.norm_mul_coe_unitary]
  have hc : u.val*(b:Unitization ℂ B)-(b:Unitization ℂ B)*u.val=
      ((u.val.snd*b-b*u.val.snd : B):Unitization ℂ B) := by
    apply Unitization.ext
    · simp [sub_eq_add_neg]
    · simp only [sub_eq_add_neg,Unitization.snd_add,Unitization.snd_neg,Unitization.snd_mul,Unitization.fst_inr,
        Unitization.snd_inr,zero_smul,add_zero,zero_add]
      abel
  rw [hc,Unitization.norm_inr]

end

end WeakPureInfiniteness
end

end OAI
