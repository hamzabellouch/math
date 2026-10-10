import OAI.Algebra.AuslanderReiten.Duality.DualTensorEvaluation
import OAI.Algebra.AuslanderReiten.Duality.RightDual

namespace OAI

noncomputable section
namespace ArExplicit.DualTensor
variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
variable [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def moduleEvaluation : BalancedTensor k R (Coinduced k R) V →ₗ[R]
    RightDual k R (V →ₗ[R] R) where
  toFun z := ⟨evaluation z⟩
  map_add' x y := by apply RightDual.ext; exact map_add evaluation x y
  map_smul' r z := by
    apply RightDual.ext
    ext f
    exact evaluation_left r z f

@[simp] theorem moduleEvaluation_tmul (φ : Coinduced k R) (v : V) (f : V →ₗ[R] R) :
    (moduleEvaluation (BalancedTensor.tmul φ v)).functional f = φ.functional (f v) := rfl

def moduleEvaluationEquiv [Module.Finite R V] [Module.Projective R V] :
    BalancedTensor k R (Coinduced k R) V ≃ₗ[R] RightDual k R (V →ₗ[R] R) :=
  LinearEquiv.ofBijective moduleEvaluation
    ((RightDual.scalarEquiv (k := k) (R := R)).symm.bijective.comp evaluation_bijective)

def precomposeRight (a : V →ₗ[R] W) : (W →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (V →ₗ[R] R) where
  toFun f := f.comp a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem moduleEvaluation_natural (a : V →ₗ[R] W)
    (z : BalancedTensor k R (Coinduced k R) V) :
    moduleEvaluation (BalancedTensor.mapRight (S := R) a z) =
      RightDual.map (precomposeRight a) (moduleEvaluation z) := by
  apply RightDual.ext
  ext f
  exact evaluation_natural a z f

end ArExplicit.DualTensor

end

end OAI
