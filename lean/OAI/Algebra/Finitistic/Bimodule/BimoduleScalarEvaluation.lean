import OAI.Algebra.Finitistic.Bimodule.BimoduleSingleEvaluation

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N] [hN : IsScalarTower k B N]
abbrev CanonicalInput := BalancedTensor.ScalarLeftModule k B (ModuleCat.of B N)

variable (M : ModuleCat.{u} (Enveloping k B))

def toNativeScalar : BimoduleBalancedTensor.Tensor k B M (CanonicalInput k B N) →ₗ[B]
    BimoduleBalancedTensor.Tensor k B M N where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    (CanonicalInput k B N) N _ _ _ _ _ _
    _ _ _ (BalancedTensor.scalarLeftTower k B (ModuleCat.of B N)) _ _ _ hN (LinearMap.id : CanonicalInput k B N →ₗ[B] N)).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

def fromNativeScalar : BimoduleBalancedTensor.Tensor k B M N →ₗ[B]
    BimoduleBalancedTensor.Tensor k B M (CanonicalInput k B N) where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    N (CanonicalInput k B N) _ _ _ _ _ _
    _ _ _ hN _ _ _ (BalancedTensor.scalarLeftTower k B (ModuleCat.of B N)) (LinearMap.id : N →ₗ[B] CanonicalInput k B N)).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

/-- Canonical restriction and the native compatible k action give the same B-valued tensor. -/
def scalarTensorIso :
    (BimoduleBalancedTensor.functor k B (CanonicalInput k B N)).obj M ≅
      (BimoduleBalancedTensor.functor k B N).obj M where
  hom := ModuleCat.ofHom (toNativeScalar k B N M)
  inv := ModuleCat.ofHom (fromNativeScalar k B N M)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {M} {M' : ModuleCat.{u} (Enveloping k B)}
theorem scalarTensor_natural (f : M ⟶ M') :
    (BimoduleBalancedTensor.functor k B (CanonicalInput k B N)).map f ≫ (scalarTensorIso k B N M').hom =
      (scalarTensorIso k B N M).hom ≫ (BimoduleBalancedTensor.functor k B N).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Exact comparison to native module evaluation with its original compatible scalar structure. -/
def scalarEvaluationIso (P : BiComplex k B) :
    moduleEvaluation k B P (ModuleCat.of B N) ≅
      ((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => scalarTensorIso k B N (P.X n))
    (fun n m _ => (scalarTensor_natural k B N (P.d n m)).symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
