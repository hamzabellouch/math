import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Algebra.Opposite

namespace OAI

namespace ArExplicit

open TensorProduct

variable (k R F M : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]

def balancingRelations : Submodule k (F ⊗[k] M) :=
  Submodule.span k {z | ∃ (f : F) (r : R) (m : M),
    z = (MulOpposite.op r • f) ⊗ₜ[k] m - f ⊗ₜ[k] (r • m)}

abbrev BalancedTensor := (F ⊗[k] M) ⧸ balancingRelations k R F M

namespace BalancedTensor

variable {k R F M}

def tmul (f : F) (m : M) : BalancedTensor k R F M :=
  (balancingRelations k R F M).mkQ (f ⊗ₜ[k] m)

@[simp] theorem zero_tmul (m : M) : tmul (k := k) (R := R) (0 : F) m = 0 := by
  simp [tmul]

@[simp] theorem tmul_zero (f : F) : tmul (k := k) (R := R) f (0 : M) = 0 := by
  simp [tmul]

theorem add_tmul (f g : F) (m : M) :
    tmul (k := k) (R := R) (f + g) m = tmul f m + tmul g m := by simp [tmul, TensorProduct.add_tmul]

theorem tmul_add (f : F) (m n : M) :
    tmul (k := k) (R := R) f (m + n) = tmul f m + tmul f n := by simp [tmul, TensorProduct.tmul_add]

theorem scalar_tmul (c : k) (f : F) (m : M) :
    tmul (k := k) (R := R) (c • f) m = c • tmul f m := by
  exact (balancingRelations k R F M).mkQ.map_smul c (f ⊗ₜ[k] m)

theorem tmul_scalar (c : k) (f : F) (m : M) :
    tmul (k := k) (R := R) f (c • m) = c • tmul f m := by simp [tmul]

theorem balance (f : F) (r : R) (m : M) :
    tmul (k := k) (R := R) (MulOpposite.op r • f) m = tmul f (r • m) := by
  apply (Submodule.Quotient.eq (balancingRelations k R F M)).mpr
  exact Submodule.subset_span ⟨f, r, m, rfl⟩

def mk : F →ₗ[k] M →ₗ[k] BalancedTensor k R F M where
  toFun f :=
    { toFun := tmul f
      map_add' := tmul_add f
      map_smul' := fun c m => tmul_scalar c f m }
  map_add' f g := by ext m; exact add_tmul f g m
  map_smul' c f := by ext m; exact scalar_tmul c f m

variable {N : Type*} [AddCommGroup N] [Module k N]

def lift (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m)) :
    BalancedTensor k R F M →ₗ[k] N :=
  (balancingRelations k R F M).liftQ (TensorProduct.lift b) (by
    apply Submodule.span_le.mpr
    rintro z ⟨f, r, m, rfl⟩
    change TensorProduct.lift b ((MulOpposite.op r • f) ⊗ₜ[k] m - f ⊗ₜ[k] (r • m)) = 0
    simp only [map_sub, TensorProduct.lift.tmul, hb, sub_self])

@[simp] theorem lift_tmul (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m)) (f : F) (m : M) :
    lift b hb (tmul f m) = b f m := rfl

@[ext] theorem hom_ext (f g : BalancedTensor k R F M →ₗ[k] N)
    (h : ∀ x y, f (tmul x y) = g (tmul x y)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact h x y
      | add z z' hz hz' =>
          change f ((balancingRelations k R F M).mkQ (z + z')) =
            g ((balancingRelations k R F M).mkQ (z + z'))
          simp only [map_add]
          exact congrArg₂ (· + ·) hz hz'

end BalancedTensor
end ArExplicit

end OAI
