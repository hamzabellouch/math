import OAI.Algebra.AuslanderReiten.Evaluation.CanonicalRegularEndpoint
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationCoefficient

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

def endpointWithCoefficients (e : X ≅ Y) :
    (EnvelopingBimodule.evaluationFunctor k R X).obj (AbsoluteBar.moduleObject k R 0) ⟶ Y :=
  (EnvelopingBimodule.evaluationCoefficientIso k R e).hom.app (AbsoluteBar.moduleObject k R 0) ≫
    (nativeEndpointIso k R Y).hom

theorem endpointWithCoefficients_tmul (e : X ≅ Y)
    (a : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    endpointWithCoefficients k R X Y e (BalancedTensor.tmul a x) =
      e.hom ((show R from a.value) • x) := by
  change (nativeEndpointIso k R Y).hom
    ((EnvelopingBimodule.evaluationCoefficientIso k R e).hom.app
      (AbsoluteBar.moduleObject k R 0) (BalancedTensor.tmul a x)) = _
  rw [EnvelopingBimodule.evaluationCoefficientIso_tmul, nativeEndpointIso_tmul_value]
  exact (e.hom.hom.map_smul _ _).symm

end ArExplicit.BarBalanced

end

end OAI
