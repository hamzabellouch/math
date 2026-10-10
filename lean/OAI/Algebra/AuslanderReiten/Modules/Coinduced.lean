import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

namespace ArExplicit

@[ext] structure Coinduced (k R : Type*) [CommRing k] [Ring R] [Algebra k R] where
  functional : Module.Dual k R

namespace Coinduced

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

def coordinates : Coinduced k R ≃ Module.Dual k R where
  toFun := functional
  invFun := Coinduced.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Coinduced k R) := coordinates.addCommGroup
instance : Module k (Coinduced k R) := coordinates.addEquiv.module k

@[simp] theorem functional_zero (s : R) : (0 : Coinduced k R).functional s = 0 := rfl
@[simp] theorem functional_add (x y : Coinduced k R) (s : R) :
    (x + y).functional s = x.functional s + y.functional s := rfl
@[simp] theorem functional_smul (c : k) (x : Coinduced k R) (s : R) :
    (c • x).functional s = c * x.functional s := rfl

def action (r : R) (x : Coinduced k R) : Coinduced k R :=
  ⟨{ toFun := fun s => x.functional (s * r)
     map_add' := fun s t => by simp [add_mul]
     map_smul' := fun c s => by simp }⟩

instance : SMul R (Coinduced k R) := ⟨action⟩

@[simp] theorem functional_action (r : R) (x : Coinduced k R) (s : R) :
    (r • x).functional s = x.functional (s * r) := rfl

instance : Module R (Coinduced k R) where
  one_smul x := by ext s; simp
  mul_smul r s x := by ext t; simp [mul_assoc]
  smul_zero r := by ext s; simp
  smul_add r x y := by ext s; simp
  zero_smul x := by ext s; simp
  add_smul r s x := by ext t; simp [mul_add]

instance : IsScalarTower k R (Coinduced k R) where
  smul_assoc c r x := by ext s; simp

instance : SMulCommClass k R (Coinduced k R) where
  smul_comm c r x := by ext s; rfl

def scalarLinearEquiv : Coinduced k R ≃ₗ[k] Module.Dual k R :=
  coordinates.addEquiv.linearEquiv k

def evalOne : Coinduced k R →ₗ[k] k where
  toFun x := x.functional 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fromFunctional (φ : Module.Dual k R) : R →ₗ[R] Coinduced k R where
  toFun r := action r ⟨φ⟩
  map_add' r s := by ext t; simp [action, mul_add]
  map_smul' r s := by
    ext t
    change φ (t * (r * s)) = φ ((t * r) * s)
    exact congrArg φ (mul_assoc t r s).symm

section Field

variable {k : Type*} [Field k] {R : Type*} [Ring R] [Algebra k R]

instance : Module.Injective R (Coinduced k R) := by
  apply Module.Baer.injective
  intro I g
  let φ : (I.restrictScalars k) →ₗ[k] k := evalOne.comp (g.restrictScalars k)
  obtain ⟨ψ, hψ⟩ := φ.exists_extend
  refine ⟨fromFunctional ψ, ?_⟩
  intro x hx
  apply Coinduced.ext
  ext r
  have h := LinearMap.congr_fun hψ (r • (⟨x, hx⟩ : I))
  change ψ (r * x) = (g ⟨x, hx⟩).functional r
  change ψ (r * x) = (g (r • (⟨x, hx⟩ : I))).functional 1 at h
  rw [map_smul] at h
  simpa using h

instance [Module.Finite k R] : Module.Finite k (Coinduced k R) :=
  Module.Finite.equiv scalarLinearEquiv.symm

theorem finrank_eq [Module.Finite k R] :
    Module.finrank k (Coinduced k R) = Module.finrank k R := by
  rw [scalarLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]

end Field
end Coinduced
end ArExplicit

end OAI
