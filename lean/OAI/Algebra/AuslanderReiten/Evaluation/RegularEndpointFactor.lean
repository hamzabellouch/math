import OAI.Algebra.AuslanderReiten.Evaluation.RegularCoefficientNaturality
import OAI.Algebra.AuslanderReiten.Bar.AugmentedBarEvaluation

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
local instance : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
local instance : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)

def regularAction :
    (EnvelopingBimodule.evaluationFunctor k R X).obj (AbsoluteBar.moduleObject k R 0) ⟶ X :=
  (endpointWithCoefficients k R X (ModuleCat.of R X) (Iso.refl X))

theorem endpointWithCoefficients_factor (e : X ≅ Y) :
    endpointWithCoefficients k R X Y e = regularAction k R X ≫ e.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.hom_ext
  intro a x
  change endpointWithCoefficients k R X Y e (BalancedTensor.tmul a x) =
    e.hom (endpointWithCoefficients k R X (ModuleCat.of R X) (Iso.refl X) (BalancedTensor.tmul a x))
  rw [endpointWithCoefficients_tmul, endpointWithCoefficients_tmul]
  rfl

end ArExplicit.BarBalanced

end

end OAI
