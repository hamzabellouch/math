import OAI.Algebra.Finitistic.Tensor.BalancedTensor
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.Algebra.Algebra.Opposite

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable {M N : Type u} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def mapRight (f : M →ₗ[A] N) : BalancedTensor.Tensor k A U M →ₗ[k]
    BalancedTensor.Tensor k A U N :=
  BalancedTensor.lift
    ((BalancedTensor.mk k A U N).compl₁₂ LinearMap.id (f.restrictScalars k)) (by
      intro a u m
      change BalancedTensor.mk k A U N (MulOpposite.op a • u) (f m) =
        BalancedTensor.mk k A U N u (f (a • m))
      rw [f.map_smul, BalancedTensor.balance])

@[simp] theorem mapRight_mk (f : M →ₗ[A] N) (u : U) (m : M) :
    mapRight (k := k) U f (BalancedTensor.mk k A U M u m) =
      BalancedTensor.mk k A U N u (f m) := rfl

omit [Algebra k A] [IsScalarTower k A N] in
/-- Radical multiplication is killed by tensor with any right module
annihilated by the ring radical. -/
theorem mk_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (n : N) (hn : n ∈ Ring.jacobson A • (⊤ : Submodule A N)) (u : U) :
    BalancedTensor.mk k A U N u n = 0 := by
  let K : Submodule A N :=
    { carrier := {n | ∀ u : U, BalancedTensor.mk k A U N u n = 0}
      zero_mem' := fun u => map_zero _
      add_mem' := fun hx hy u => by rw [map_add, hx, hy, add_zero]
      smul_mem' := fun a x hx u => by rw [← BalancedTensor.balance]; exact hx _ }
  have hK : Ring.jacobson A • (⊤ : Submodule A N) ≤ K := by
    apply Submodule.smul_le.mpr
    intro a ha x _ u
    rw [← BalancedTensor.balance, hU a ha u]
    exact LinearMap.congr_fun (map_zero (BalancedTensor.mk k A U N)) x
  exact hK hn u

theorem mapRight_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (f : M →ₗ[A] N)
    (hf : LinearMap.range f ≤ Ring.jacobson A • (⊤ : Submodule A N)) :
    mapRight (k := k) U f = 0 := by
  apply BalancedTensor.ext
  intro u m
  exact mk_radical_zero (k := k) U hU (f m) (hf (mem_range_self f m)) u

/-- The actual right radical quotient of the regular module. -/
def rightRadical : Submodule Aᵐᵒᵖ A where
  carrier := Ring.jacobson A
  zero_mem' := (Ring.jacobson A).zero_mem
  add_mem' := (Ring.jacobson A).add_mem
  smul_mem' b _ ha := (Ring.jacobson A).mul_mem_right b.unop ha

abbrev Residue := A ⧸ (rightRadical (A := A))

theorem residue_annihilated (a : A) (ha : a ∈ Ring.jacobson A) (s : Residue (A := A)) :
    MulOpposite.op a • s = 0 := by
  induction s using Submodule.Quotient.induction_on with
  | _ b =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (Ring.jacobson A).mul_mem_left b ha
end LittleFinitistic.PDTensor

end

end OAI
