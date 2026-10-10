import OAI.Algebra.AuslanderReiten.Modules.InductionBimodule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorUnit

namespace OAI

noncomputable section
namespace ArExplicit
namespace Induction

variable {k R S V W : Type*} [CommRing k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S)
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [Module S W]
  [IsScalarTower k R W] [IsScalarTower k S W]

abbrev Object := BalancedTensor k R (InductionBimodule ι) V

def restrictHom (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (f : Object (V := V) ι →ₗ[S] W) : V →ₗ[R] W where
  toFun v := f (BalancedTensor.tmul ⟨1⟩ v)
  map_add' x y := by rw [BalancedTensor.tmul_add, map_add]
  map_smul' r v := by
    rw [← BalancedTensor.balance]
    change f (BalancedTensor.tmul ⟨1 * ι r⟩ v) = r • f (BalancedTensor.tmul ⟨1⟩ v)
    rw [one_mul, hcompat]
    have he : BalancedTensor.tmul (InductionBimodule.mk (ι r)) v =
        (ι r) • (BalancedTensor.tmul (InductionBimodule.mk (1 : S)) v : Object (V := V) ι) := by
      change BalancedTensor.tmul (InductionBimodule.mk (ι r)) v =
        BalancedTensor.tmul (InductionBimodule.mk (ι r * 1)) v
      rw [mul_one]
    rw [he, f.map_smul]

def extendFormula (g : V →ₗ[R] W) : InductionBimodule ι →ₗ[k] V →ₗ[k] W :=
  ((BalancedTensor.leftAction (k := k) (R := S) (M := W)).compl₂
    (g.restrictScalars k)).comp (InductionBimodule.scalarEquiv ι).toLinearMap

def extendHom (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (g : V →ₗ[R] W) : Object (V := V) ι →ₗ[S] W :=
  BalancedTensor.liftLeft (extendFormula ι g)
    (by
      intro a r v
      change (a.value * ι r) • g v = a.value • g (r • v)
      rw [g.map_smul, hcompat, mul_smul])
    (by intro s a v; exact mul_smul s a.value (g v))

@[simp] theorem extendHom_tmul (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (g : V →ₗ[R] W) (a : InductionBimodule ι) (v : V) :
    extendHom ι hcompat g (BalancedTensor.tmul a v) = a.value • g v := rfl

def homEquiv (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w) :
    (Object (V := V) ι →ₗ[S] W) ≃ₗ[k] (V →ₗ[R] W) where
  toFun := restrictHom ι hcompat
  invFun := extendHom ι hcompat
  left_inv f := by
    apply BalancedTensor.leftHom_ext
    intro a v
    change a.value • f (BalancedTensor.tmul ⟨1⟩ v) = f (BalancedTensor.tmul a v)
    rw [← f.map_smul]
    congr 1
    change BalancedTensor.tmul ⟨a.value * 1⟩ v = BalancedTensor.tmul a v
    rw [mul_one]
  right_inv g := by
    apply LinearMap.ext
    intro v
    exact one_smul S (g v)
  map_add' f g := by
    apply LinearMap.ext
    intro v
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro v
    rfl

end Induction
end ArExplicit

end

end OAI
