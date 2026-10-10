import OAI.Algebra.AuslanderReiten.Resolutions.TrivialInductionQuotient
import OAI.Algebra.AuslanderReiten.Duality.DualTensorComplex

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

def dualInflateEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (Coinduced k R) M ≃ₗ[T]
      (inflate (k := k)).obj
        (ModuleCat.of R (BalancedTensor k R (Coinduced k R) M)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t z := by
    change t • z = t.base • z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul φ m => rfl

def dualFunctorIso :
    BalancedTensor.functor (k := k) (R := R) (S := T) (F := Coinduced k R) ≅
      BalancedTensor.functor (k := k) (R := R) (S := R) (F := Coinduced k R) ⋙ inflate :=
  NatIso.ofComponents (fun M => (dualInflateEquiv M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

def dualComplexIso {ι : Type*} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    dualComplex (k := k) P ≅
      ((inflate (k := k)).mapHomologicalComplex c).obj
        (((BalancedTensor.functor (k := k) (R := R) (S := R)
          (F := Coinduced k R)).mapHomologicalComplex c).obj P) :=
  (NatIso.mapHomologicalComplex dualFunctorIso c).app P

end ArExplicit.TrivialInduction

end

end OAI
