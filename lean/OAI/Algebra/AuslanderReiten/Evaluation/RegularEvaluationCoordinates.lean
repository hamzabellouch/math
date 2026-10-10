import OAI.Algebra.AuslanderReiten.Evaluation.RegularEndpointFactor
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedEquiv

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X Y : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
local instance : Module k Y := moduleCatBaseModule (k := k) (R := R) Y
local instance : IsScalarTower k R Y := moduleCatBaseTower (k := k) (R := R) Y
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
local instance : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
local instance : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
variable (e : M ≃ₗ[R ⊗[k] Rᵐᵒᵖ] AbsoluteBar.moduleObject k R 0)

def nativeRegularCoordinates :
    BalancedTensor k R (EnvelopingBimodule k R M) X ≃ₗ[R] X := by
  letI := AbsoluteBar.baseModule k R 0
  letI := AbsoluteBar.bimoduleTower k R 0
  exact (EnvelopingBimodule.tensorCongr e X).trans (zeroEvaluationEquiv k R X)

@[simp] theorem nativeRegularCoordinates_tmul
    (m : EnvelopingBimodule k R M) (x : X) :
    nativeRegularCoordinates k R X M e (BalancedTensor.tmul m x) =
      (show R from e m.value) • x := rfl

theorem regularCoordinates_factor (u : X ≅ Y) :
    (endpointWithCoefficients k R X Y u).hom.comp
      (EnvelopingBimodule.tensorMap X e.toModuleIso.hom) =
      u.hom.hom.comp (nativeRegularCoordinates k R X M e).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.hom_ext
  intro m x
  change endpointWithCoefficients k R X Y u
    (BalancedTensor.tmul (EnvelopingBimodule.map e.toModuleIso.hom m) x) = _
  rw [endpointWithCoefficients_tmul]
  rfl

end ArExplicit.BarBalanced

end

end OAI
