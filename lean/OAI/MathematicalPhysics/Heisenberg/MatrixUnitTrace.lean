import OAI.MathematicalPhysics.Heisenberg.TensorLiftIndex

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [Field R] [CharZero R] [Ring E] [Algebra R E] [Fintype K] [DecidableEq K] [Nonempty K]

lemma trace_unit (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (hs : ∑ a,u a a=1) (τ : E →ₗ[R] R) (hτ : ∀ A B,τ (A*B)=τ (B*A))
    (h1 : τ 1=1) (a b : K) :
    τ (u a b)=if a=b then (Fintype.card K:R)⁻¹ else 0 := by
  have hd (a b : K) : τ (u a a)=τ (u b b) := by
    have hh:=hτ (u a b) (u b a)
    simpa only [hu,ite_true] using hh
  by_cases hab : a=b
  · subst b
    rw [ite_eq_left rfl]
    have hh:=congrArg τ hs
    rw [map_sum,h1] at hh
    simp_rw [hd _ a] at hh
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
    apply (mul_left_cancel₀ (show (Fintype.card K:R)≠0 by exact_mod_cast Fintype.card_ne_zero))
    rw [hh,mul_inv_cancel₀ (show (Fintype.card K:R)≠0 by exact_mod_cast Fintype.card_ne_zero)]
  · rw [ite_eq_right hab]
    have hh:=hτ (u a b) (u b b)
    simpa only [hu,ite_true,ite_eq_right (Ne.symm hab),map_zero] using hh

lemma trace_lift (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (hs : ∑ a,u a a=1) (τ : E →ₗ[R] R) (hτ : ∀ A B,τ (A*B)=τ (B*A))
    (h1 : τ 1=1) (M : Matrix K K R) :
    τ (liftAlg u hu hs M)=(Fintype.card K:R)⁻¹*Matrix.trace M := by
  rw [liftAlg_apply]
  simp only [map_sum,map_smul,trace_unit u hu hs τ hτ h1,smul_eq_mul,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Matrix.trace,←Finset.sum_mul]
  exact mul_comm _ _

end Heisenberg.TensorUnits
end
end

end OAI
