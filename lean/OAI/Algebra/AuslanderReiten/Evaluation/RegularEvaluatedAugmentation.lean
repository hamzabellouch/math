import OAI.Algebra.AuslanderReiten.Evaluation.RegularEvaluationCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X Y : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
local instance : Module k Y := moduleCatBaseModule (k := k) (R := R) Y
local instance : IsScalarTower k R Y := moduleCatBaseTower (k := k) (R := R) Y
variable (P Q : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
local instance : Module k Q := moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) Q
local instance : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) Q
local instance : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
local instance : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)

variable (u : X ≅ Y) (f : P ⟶ Q)
variable (e : Q ≃ₗ[R ⊗[k] Rᵐᵒᵖ] AbsoluteBar.moduleObject k R 0)
variable (b : P ⟶ AbsoluteBar.moduleObject k R 0)

theorem regularEvaluatedAugmentation (hb : f ≫ e.toModuleIso.hom = b) :
    (EnvelopingBimodule.evaluationFunctor k R X).map b ≫
      endpointWithCoefficients k R X Y u =
    (EnvelopingBimodule.evaluationFunctor k R X).map f ≫
      (nativeRegularCoordinates k R X Q e).toModuleIso.hom ≫ u.hom := by
  have he : (EnvelopingBimodule.evaluationFunctor k R X).map e.toModuleIso.hom ≫
      endpointWithCoefficients k R X Y u =
      (nativeRegularCoordinates k R X Q e).toModuleIso.hom ≫ u.hom :=
    ModuleCat.hom_ext (regularCoordinates_factor k R X Y Q e u)
  rw [← hb, (EnvelopingBimodule.evaluationFunctor k R X).map_comp, Category.assoc, he]
  rfl

end ArExplicit.BarBalanced

end

end OAI
