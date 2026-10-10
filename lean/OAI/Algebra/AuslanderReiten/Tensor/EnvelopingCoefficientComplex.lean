import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationCoefficient
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable {X Y : ModuleCat.{u} R}
variable [Module k X] [IsScalarTower k R X] [Module k Y] [IsScalarTower k R Y]
variable (e : X ≅ Y) (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)

def coefficientComplexIso :
    ((evaluationFunctor k R X).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ≅
      ((evaluationFunctor k R Y).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  (NatIso.mapHomologicalComplex (evaluationCoefficientIso k R e) (ComplexShape.down ℕ)).app P

theorem coefficientComplexIso_comparison (m n : ℕ) (f : P.X m ⟶ P.X n) :
    (evaluationFunctor k R X).map f ≫ (coefficientComplexIso k R e P).hom.f n =
      (coefficientComplexIso k R e P).hom.f m ≫ (evaluationFunctor k R Y).map f :=
  (evaluationCoefficientIso k R e).hom.naturality f

end ArExplicit.EnvelopingBimodule

end

end OAI
