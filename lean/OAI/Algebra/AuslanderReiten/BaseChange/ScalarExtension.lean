import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w

section BaseChange

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [Module R M] [Module k M]
  [IsScalarTower k R M]

def scalarExtensionRepresentation :
    E ⊗[k] R →ₐ[E] Module.End E (E ⊗[k] M) :=
  AlgHom.liftEquiv k E R (Module.End E (E ⊗[k] M))
    ((Module.End.baseChangeHom k E M).comp (Algebra.lsmul k k M))

@[instance_reducible]
def scalarExtensionModule : Module (E ⊗[k] R) (E ⊗[k] M) :=
  Module.compHom (E ⊗[k] M) (scalarExtensionRepresentation k E R M).toRingHom

attribute [local instance] scalarExtensionModule

theorem scalarExtension_smul_tmul (e e' : E) (r : R) (m : M) :
    (e ⊗ₜ[k] r) • (e' ⊗ₜ[k] m) = (e * e') ⊗ₜ[k] (r • m) := by
  change ((scalarExtensionRepresentation k E R M) (e ⊗ₜ[k] r)) (e' ⊗ₜ[k] m) = _
  rfl

instance scalarExtensionIsScalarTower :
    IsScalarTower E (E ⊗[k] R) (E ⊗[k] M) :=
  IsScalarTower.of_algebraMap_smul fun e x => by
    change ((scalarExtensionRepresentation k E R M)
      (algebraMap E (E ⊗[k] R) e)) x = e • x
    rw [AlgHom.commutes]
    rfl

instance scalarExtensionBaseIsScalarTower :
    IsScalarTower k (E ⊗[k] R) (E ⊗[k] M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    rw [IsScalarTower.algebraMap_apply k E (E ⊗[k] R),
      IsScalarTower.algebraMap_smul (E ⊗[k] R), IsScalarTower.algebraMap_smul E]

end BaseChange

section Maps

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def scalarExtensionMap (f : M →ₗ[R] N) :
    (E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N) where
  toAddHom := ((f.restrictScalars k).baseChange E).toAddHom
  map_smul' a x := by
    change ((f.restrictScalars k).baseChange E) (a • x) =
      a • ((f.restrictScalars k).baseChange E) x
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | tmul e r =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul e' m =>
        simp only [scalarExtension_smul_tmul, LinearMap.baseChange_tmul,
          LinearMap.restrictScalars_apply, map_smul]

@[simp]
theorem scalarExtensionMap_tmul (f : M →ₗ[R] N) (e : E) (m : M) :
    scalarExtensionMap k E R f (e ⊗ₜ[k] m) = e ⊗ₜ[k] f m := rfl

@[simp]
theorem scalarExtensionMap_id :
    scalarExtensionMap k E R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul e m => rfl

@[simp]
theorem scalarExtensionMap_comp (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    scalarExtensionMap k E R (g.comp f) =
      (scalarExtensionMap k E R g).comp (scalarExtensionMap k E R f) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul e m => rfl

end Maps

end ArExplicit

end

end OAI
