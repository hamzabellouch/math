import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingEndpoint
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFiniteEvaluation
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctorExt

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R
  (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) M.carrier ≃ₗ[R] M.carrier)
variable (E : M.carrier ≅ (ModuleCat.restrictScalars σ.symm.toRingHom).obj M.carrier)

theorem twistedFiniteEndpoint_eq
    (h : ∀ (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M.carrier),
      E.inv.hom (σ.symm a.value.value • m) = e (BalancedTensor.tmul a m)) :
    (twistedEnvelopingRestrictionIso σ).app M.carrier ≪≫ E.symm =
      BalancedTensor.nativeEvaluationIso M e := by
  apply BalancedTensor.functorIso_ext M.carrier M.carrier
  intro a m
  exact (twistedEnvelopingEndpoint_tmul σ M.carrier M.carrier E.symm a m).trans
    ((h a m).trans (BalancedTensor.nativeEvaluationIso_tmul M e a m).symm)

theorem twistedFiniteEndpoint_symm_eq
    (h : ∀ (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M.carrier),
      E.inv.hom (σ.symm a.value.value • m) = e (BalancedTensor.tmul a m)) :
    (BalancedTensor.nativeEvaluationIso M e).symm =
      E ≪≫ ((twistedEnvelopingRestrictionIso σ).app M.carrier).symm := by
  rw [← twistedFiniteEndpoint_eq σ M e E h]
  rfl

end ArExplicit

end

end OAI
