import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationFunctor
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMapEquiv

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable {X Y : ModuleCat.{u} R}
variable [Module k X] [IsScalarTower k R X] [Module k Y] [IsScalarTower k R Y]

def evaluationCoefficientMap (f : X ⟶ Y) :
    evaluationFunctor k R X ⟶ evaluationFunctor k R Y where
  app M := ModuleCat.ofHom (BalancedTensor.mapRight (k := k) (S := R)
    (F := EnvelopingBimodule k R M) f.hom)
  naturality {M N} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change BalancedTensor.mapRight (k := k) (S := R) f.hom (tensorMap X g z) =
      tensorMap Y g (BalancedTensor.mapRight (k := k) (S := R) f.hom z)
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z w hz hw => simp only [_root_.map_add, hz, hw]
    | tmul m x => rfl

def evaluationCoefficientIso (e : X ≅ Y) :
    evaluationFunctor k R X ≅ evaluationFunctor k R Y :=
  NatIso.ofComponents
    (fun M => (BalancedTensor.mapRightEquiv (k := k) (S := R)
      (F := EnvelopingBimodule k R M) e.toLinearEquiv).toModuleIso)
    (fun g => (evaluationCoefficientMap k R e.hom).naturality g)

@[simp] theorem evaluationCoefficientIso_tmul (e : X ≅ Y)
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (m : EnvelopingBimodule k R M) (x : X) :
    (evaluationCoefficientIso k R e).hom.app M (BalancedTensor.tmul m x) =
      BalancedTensor.tmul m (e.hom x) := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
