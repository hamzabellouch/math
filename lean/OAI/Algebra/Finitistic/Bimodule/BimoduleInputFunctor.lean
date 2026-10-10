import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTerms

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))

abbrev InputTensor (N : ModuleCat.{u} B) :=
  BimoduleBalancedTensor.Tensor k B M (BalancedTensor.ScalarLeftModule k B N)

def inputModuleMap {N N' : ModuleCat.{u} B} (f : N ⟶ N') :
    InputTensor k B M N →ₗ[B] InputTensor k B M N' where
  __ := (@BalancedTensor.mapRightTo k B (BimoduleBalancedTensor.Input k B M)
    (BalancedTensor.ScalarLeftModule k B N) (BalancedTensor.ScalarLeftModule k B N')
    _ _ _ _ _ _ _ _ _ (BalancedTensor.scalarLeftTower k B N)
    _ _ _ (BalancedTensor.scalarLeftTower k B N') f.hom).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp_all [smul_add]

/-- Tensor by one genuine bimodule, varying the left-module input and retaining the outside action. -/
def inputFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u} B where
  obj N := ModuleCat.of B (InputTensor k B M N)
  map f := ModuleCat.ofHom (inputModuleMap k B M f)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

instance inputFunctor_additive : (inputFunctor k B M).Additive where
  map_add {N N'} {f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => exact (BalancedTensor.mk k B _ _ m).map_add _ _
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

abbrev columnFunctor (P : BiComplex k B) (p : ℤ) :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ) ⋙ shiftFunctor _ (-p)

instance columnFunctor_additive (P : BiComplex k B) (p : ℤ) :
    (columnFunctor k B P p).Additive := by unfold columnFunctor; infer_instance

end LittleFinitistic.BimoduleTotal

end

end OAI
