import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingCoefficientComplex

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

theorem coefficientComplexIso_f (n : ℕ) :
    (coefficientComplexIso k R e P).hom.f n = (evaluationCoefficientIso k R e).hom.app (P.X n) := rfl

theorem coefficientComplexIso_tmul (n : ℕ) (z : EnvelopingBimodule k R (P.X n)) (x : X) :
    (coefficientComplexIso k R e P).hom.f n (BalancedTensor.tmul z x) =
      BalancedTensor.tmul z (e.hom x) := by
  rw [coefficientComplexIso_f]
  exact evaluationCoefficientIso_tmul k R e (P.X n) z x

end ArExplicit.EnvelopingBimodule

end

end OAI
