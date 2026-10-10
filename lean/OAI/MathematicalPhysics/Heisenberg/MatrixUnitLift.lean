import OAI.MathematicalPhysics.Heisenberg.TensorUnitSystem

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

def liftLinear (u : K → K → E) : Matrix K K R →ₗ[R] E where
  toFun M:=∑ a,∑ b,M a b • u a b
  map_add' M N:=by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c M:=by simp only [Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

lemma unit_mul_lift (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (a b : K) (N : Matrix K K R) :
    u a b*liftLinear u N=∑ d,N b d • u a d := by
  simp only [liftLinear,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum,mul_smul_comm,hu]
  simp only [smul_ite,smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma lift_mul (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (M N : Matrix K K R) : liftLinear u (M*N)=liftLinear u M*liftLinear u N := by
  change (∑ a,∑ b,(M*N) a b • u a b)=(∑ a,∑ b,M a b • u a b)*liftLinear u N
  simp only [Matrix.mul_apply,Finset.sum_smul,Finset.sum_mul,smul_mul_assoc,
    unit_mul_lift u hu,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

lemma lift_one (u : K → K → E) (hu : ∑ a,u a a=1) : liftLinear u (1:Matrix K K R)=1 := by
  unfold liftLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Matrix.one_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact hu

def liftAlg (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (hs : ∑ a,u a a=1) : Matrix K K R →ₐ[R] E :=
  AlgHom.ofLinearMap (liftLinear u) (lift_one u hs) (lift_mul u hu)

lemma liftAlg_apply (u : K → K → E)
    (hu : ∀ a b c d,u a b*u c d=if b=c then u a d else 0)
    (hs : ∑ a,u a a=1) (M : Matrix K K R) :
    liftAlg u hu hs M=∑ a,∑ b,M a b • u a b := rfl

end Heisenberg.TensorUnits
end

end OAI
