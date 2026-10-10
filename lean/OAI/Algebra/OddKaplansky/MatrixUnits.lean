import OAI.Algebra.OddKaplansky.FreeBlocks

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5

section
namespace OddKaplansky.MatrixUnits
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {A : Type portUniverse2} {R : Type portUniverse3} {X : Type portUniverse4} {I : Type portUniverse5} [Field K] [Ring A] [Algebra K A]
variable [Fintype R] [Fintype X] [Fintype I]
variable (u : R × X × X → A)

def lift : (R → Matrix X X K) →ₗ[K] A where
  toFun F := ∑ a : R × X × X, F a.1 a.2.1 a.2.2 • u a
  map_add' F G := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c F := by simp [mul_smul,Finset.smul_sum]
lemma lift_apply (F : R → Matrix X X K) : lift u F = ∑ r, ∑ x, ∑ y, F r x y • u (r,x,y) := by
  simp only [lift,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_prod_type]

lemma lift_injective (hu : LinearIndependent K u) : Function.Injective (lift (K := K) u) := by
  intro F G he
  funext r x y
  exact hu.eq_coords_of_eq he (r,x,y)

variable (hprod : ∀ r s x y z t, u (r,x,y) * u (s,z,t) = if r = s ∧ y = z then u (r,x,t) else 0)
include hprod in
lemma lift_mul (F G : R → Matrix X X K) : lift u F * lift u G = lift u (fun r => F r * G r) := by
  have hG (r : R) (x y : X) : u (r,x,y) * lift u G = ∑ t : X, G r y t • u (r,x,t) := by
    simp [lift_apply,Finset.mul_sum,hprod,ite_and]
  rw [lift_apply]
  simp only [Finset.sum_mul,smul_mul_assoc,hG]
  rw [lift_apply]
  simp only [Finset.smul_sum,smul_smul,Matrix.mul_apply,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_comm

include hprod in

lemma regular_rank_bound [FiniteDimensional K A] (hu : LinearIndependent K u)
    (B : Matrix X I K) (C : R → Matrix I X K) (hCB : ∀ r, C r * B = 1) :
    Fintype.card R * Fintype.card I * Fintype.card X ≤
      Module.finrank K (LinearMap.range (Algebra.lmul K A (lift u (fun r => B * C r)))) := by
  let V : (R → Matrix I X K) →ₗ[K] A := {
    toFun F := lift u (fun r => B * F r)
    map_add' F G := by simp only [Pi.add_apply,Matrix.mul_add,← map_add]; rfl
    map_smul' c F := by simp only [Pi.smul_apply,Matrix.mul_smul,← map_smul]; rfl }
  have hV : Function.Injective V := by
    intro F G he
    change lift u (fun r => B*F r) = lift u (fun r => B*G r) at he
    have hh := lift_injective u hu he
    funext r
    have hr := congrArg (fun f : R → Matrix X X K => C r * f r) hh
    simpa only [← Matrix.mul_assoc,hCB,Matrix.one_mul] using hr
  have hsub : LinearMap.range V ≤ LinearMap.range (Algebra.lmul K A (lift u (fun r => B*C r))) := by
    rintro a ⟨F,rfl⟩
    refine ⟨V F,?_⟩
    change lift u (fun r => B*C r) * lift u (fun r => B*F r) = lift u (fun r => B*F r)
    rw [lift_mul u hprod]
    congr 1
    funext r
    calc
      B*C r*(B*F r) = B*(C r*B)*F r := by simp only [Matrix.mul_assoc]
      _ = B*F r := by rw [hCB,Matrix.mul_one]
  have hfin := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj hV] at hfin
  simpa only [Module.finrank_pi_fintype,Module.finrank_matrix,Module.finrank_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,mul_one,← mul_assoc] using hfin

include hprod in
lemma lift_idempotent (T : R → Matrix X X K) (hT : ∀ r, T r * T r = T r) :
    lift u T * lift u T = lift u T := by rw [lift_mul u hprod]; congr 1; funext r; exact hT r

end
end OddKaplansky.MatrixUnits

end

end OAI
