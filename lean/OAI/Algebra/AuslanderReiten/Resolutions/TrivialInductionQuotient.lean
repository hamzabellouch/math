import OAI.Algebra.AuslanderReiten.Resolutions.TrivialInductionComplex
import OAI.Algebra.AuslanderReiten.Modules.InductionAdjunction
import OAI.Algebra.AuslanderReiten.Modules.ModuleRestriction

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

def inflate : ModuleCat.{u} R ⥤ ModuleCat.{u} T :=
  ModuleCat.restrictScalars TrivialExtension.projection.toRingHom

instance : (inflate (k := k) (R := R)).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (TrivialExtension.projection (k := k) (A := R)).toRingHom).Additive

private instance baseComm (M : ModuleCat.{u} R) : SMulCommClass k R M where
  smul_comm a r m := by
    change (algebraMap k R a) • (r • m) = r • ((algebraMap k R a) • m)
    rw [← mul_smul, Algebra.commutes a r, mul_smul]

def quotientScalarMap (M : ModuleCat.{u} R) :
    BalancedTensor k R (Quotient (k := k) (R := R)) M →ₗ[k] M :=
  BalancedTensor.lift
    ((BalancedTensor.leftAction (k := k) (R := R) (M := M)).comp
      (InductionBimodule.scalarEquiv (AlgHom.id k R)).toLinearMap)
    (by intro a r m; exact mul_smul a.value r m)

@[simp] theorem quotientScalarMap_tmul (M : ModuleCat.{u} R)
    (r : Quotient (k := k) (R := R)) (m : M) :
    quotientScalarMap M (BalancedTensor.tmul r m) = r.value • m := rfl

def quotientEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (Quotient (k := k) (R := R)) M ≃ₗ[T] (inflate (k := k)).obj M where
  toFun := quotientScalarMap M
  invFun m := BalancedTensor.tmul ⟨1⟩ m
  left_inv z := by
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, BalancedTensor.tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul r m =>
      change BalancedTensor.tmul (InductionBimodule.mk (1 : R)) (r.value • m) =
        BalancedTensor.tmul r m
      rw [← BalancedTensor.balance]
      change BalancedTensor.tmul (InductionBimodule.mk (1 * r.value)) m = _
      rw [one_mul]
  right_inv m := by
    exact @one_smul R M _ _ (show M from m)
  map_add' := (quotientScalarMap M).map_add
  map_smul' t z := by
    change quotientScalarMap M (t • z) = t.base • quotientScalarMap M z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | tmul r m => exact mul_smul t.base r.value m
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def quotientFunctorIso :
    BalancedTensor.functor (k := k) (R := R) (S := T) (F := Quotient (k := k) (R := R)) ≅ inflate :=
  NatIso.ofComponents (fun M => (quotientEquiv M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.leftHom_ext
    intro r m
    change r.value • f.hom m = f.hom (r.value • m)
    exact (f.hom.map_smul r.value m).symm)

def quotientComplexIso {ι : Type*} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    quotientComplex (k := k) P ≅ ((inflate (k := k)).mapHomologicalComplex c).obj P :=
  (NatIso.mapHomologicalComplex quotientFunctorIso c).app P

instance : (inflate (k := k) (R := R)).PreservesHomology :=
  ModuleRestriction.preservesHomology _

end ArExplicit.TrivialInduction

end

end OAI
