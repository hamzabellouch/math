import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Algebra.Tower

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u v w w' z
variable (k : Type u) [Field k] (A : Type v) [Ring A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable (N : Type w') [AddCommGroup N] [Module k N] [Module A N]

/-- Balancing relations for a right A-module and a left A-module, over k. -/
def relations : Submodule k (M ⊗[k] N) := Submodule.span k
  (Set.range fun q : A × M × N =>
    (MulOpposite.op q.1 • q.2.1) ⊗ₜ[k] q.2.2 - q.2.1 ⊗ₜ[k] (q.1 • q.2.2))

/-- Tensor over the possibly noncommutative algebra A. -/
abbrev Tensor := (M ⊗[k] N) ⧸ relations k A M N

def mk : M →ₗ[k] N →ₗ[k] Tensor k A M N :=
  (TensorProduct.mk k M N).compr₂ (relations k A M N).mkQ

variable {k A M N}

theorem balance (a : A) (m : M) (n : N) :
    mk k A M N (MulOpposite.op a • m) n = mk k A M N m (a • n) := by
  apply sub_eq_zero.mp
  change (relations k A M N).mkQ ((MulOpposite.op a • m) ⊗ₜ[k] n) -
    (relations k A M N).mkQ (m ⊗ₜ[k] (a • n)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨(a,m,n),rfl⟩)

variable {V : Type z} [AddCommGroup V] [Module k V]

/-- Universal property for k-bilinear maps satisfying the actual A-balancing equation. -/
def lift (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) : Tensor k A M N →ₗ[k] V :=
  (relations k A M N).liftQ (TensorProduct.lift f) (by
    rw [relations, Submodule.span_le]
    rintro _ ⟨⟨a,m,n⟩,rfl⟩
    change TensorProduct.lift f ((MulOpposite.op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)) = 0
    simp only [map_sub, TensorProduct.lift.tmul, hf, sub_self])

@[simp] theorem lift_mk (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) (m : M) (n : N) :
    lift f hf (mk k A M N m n) = f m n := rfl

@[elab_as_elim] theorem induction_on {C : Tensor k A M N → Prop} (x : Tensor k A M N)
    (hz : C 0) (ht : ∀ m n, C (mk k A M N m n))
    (ha : ∀ a b, C a → C b → C (a+b)) : C x := by
  classical
  by_cases zero_tensor : x = 0
  · simpa [zero_tensor] using hz
  clear zero_tensor
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction x using TensorProduct.inductionOn with
    | tmul m n => exact ht m n
    | add a b h₁ h₂ => exact ha _ _ h₁ h₂

@[ext] theorem ext {f g : Tensor k A M N →ₗ[k] V}
    (h : ∀ m n, f (mk k A M N m n) = g (mk k A M N m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | hz => simp
  | ht m n => exact h m n
  | ha a b h₁ h₂ => simp [h₁,h₂]
end LittleFinitistic.BalancedTensor

end

end OAI
