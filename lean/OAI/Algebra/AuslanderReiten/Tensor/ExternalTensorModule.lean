import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def left : A →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

def right : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

@[simp] theorem left_tmul (a : A) (m : M) (n : N) :
    left k A M N a (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] n := rfl

@[simp] theorem right_tmul (b : B) (m : M) (n : N) :
    right k B M N b (m ⊗ₜ[k] n) = m ⊗ₜ[k] (b • n) := rfl

theorem left_right (a : A) (b : B) (z : M ⊗[k] N) :
    left k A M N a (right k B M N b z) =
      right k B M N b (left k A M N a z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => rfl

def representation : (A ⊗[k] B) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift (left k A M N) (right k B M N) fun a b => by
    apply LinearMap.ext
    exact left_right k A B M N a b

@[instance_reducible] def module : Module (A ⊗[k] B) (M ⊗[k] N) :=
  Module.compHom (M ⊗[k] N) (representation k A B M N).toRingHom

def moduleObject : ModuleCat.{u} (A ⊗[k] B) :=
  letI := module k A B M N
  ModuleCat.of (A ⊗[k] B) (M ⊗[k] N)

instance baseModule : Module k (moduleObject k A B M N) :=
  inferInstanceAs (Module k (M ⊗[k] N))

instance tower : IsScalarTower k (A ⊗[k] B) (moduleObject k A B M N) :=
  IsScalarTower.of_algebraMap_smul (A := A ⊗[k] B) fun a x => by
    change representation k A B M N (algebraMap k (A ⊗[k] B) a) x = a • x
    rw [AlgHom.commutes]
    rfl

@[simp] theorem smul_tmul (a : A) (b : B) (m : M) (n : N) :
    @SMul.smul (A ⊗[k] B) (moduleObject k A B M N)
      (moduleObject k A B M N).isModule.toSMul (a ⊗ₜ[k] b) (m ⊗ₜ[k] n) =
      ((a • m) ⊗ₜ[k] (b • n) : moduleObject k A B M N) := rfl

instance finite [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (moduleObject k A B M N) :=
  inferInstanceAs (Module.Finite k (M ⊗[k] N))

variable {M N}
variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
variable [Module k M'] [Module k N'] [Module A M'] [Module B N']
variable [IsScalarTower k A M'] [IsScalarTower k B N']

def map (f : M →ₗ[A] M') (g : N →ₗ[B] N') :
    moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B M' N' where
  toAddHom := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).toAddHom
  map_smul' a z := by
    let F := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
    let w : M ⊗[k] N := z
    change F (representation k A B M N a w) = representation k A B M' N' a (F w)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul m n =>
        change (f (a • m)) ⊗ₜ[k] (g (b • n)) = (a • f m) ⊗ₜ[k] (b • g n)
        rw [map_smul, map_smul]

@[simp] theorem map_tmul (f : M →ₗ[A] M') (g : N →ₗ[B] N') (m : M) (n : N) :
    map k A B f g (m ⊗ₜ[k] n) = (f m) ⊗ₜ[k] (g n) := rfl

end ArExplicit.ExternalTensor

end

end OAI
