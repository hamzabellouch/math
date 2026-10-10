import OAI.Algebra.AuslanderReiten.Modules.TwistedModuleEvaluation
import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensorFunctor

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def twistedEnvelopingRestrictionEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M :=
  (BalancedTensor.congrLeft (twistedEvaluationCoordinates σ) (LinearEquiv.refl k M)
    (twistedEvaluationCoordinates_right σ) (fun _ _ => rfl)
    (twistedEvaluationCoordinates_left σ)).trans (TwistedBimodule.tensorRestrictionEquiv σ M)

@[simp] theorem twistedEnvelopingRestrictionEquiv_tmul (M : ModuleCat.{u} R)
    (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M) :
    twistedEnvelopingRestrictionEquiv σ M (BalancedTensor.tmul a m) =
      σ.symm a.value.value • m := rfl

def twistedEnvelopingRestrictionIso :
    BalancedTensor.functor (k := k) (R := R) (S := R)
      (F := EnvelopingBimodule k R (twistedFiniteModule σ).carrier) ≅
      ModuleCat.restrictScalars σ.symm.toRingHom :=
  NatIso.ofComponents (fun M => (twistedEnvelopingRestrictionEquiv σ M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.leftHom_ext
    intro a m
    change σ.symm a.value.value • f.hom m = f.hom (σ.symm a.value.value • m)
    exact (f.hom.map_smul _ _).symm)

instance twistedEnvelopingFunctor_equivalence :
    (BalancedTensor.functor (k := k) (R := R) (S := R)
      (F := EnvelopingBimodule k R (twistedFiniteModule σ).carrier)).IsEquivalence := by
  let := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv σ.symm.toRingEquiv
  exact Functor.isEquivalence_of_iso (twistedEnvelopingRestrictionIso σ).symm

end ArExplicit

end

end OAI
