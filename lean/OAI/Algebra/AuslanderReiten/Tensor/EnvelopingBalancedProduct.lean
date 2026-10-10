import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
  [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
  [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (X : ModuleCat.{u} R) [Module k X]
local notation "ProdMN" => ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)
local notation "EM" => BalancedTensor k R (EnvelopingBimodule k R M) X
local notation "EN" => BalancedTensor k R (EnvelopingBimodule k R N) X
local notation "EP" => BalancedTensor k R (EnvelopingBimodule k R ProdMN) X

def tensorProdMap : EP →ₗ[R] EM × EN :=
  (tensorMap (k := k) X (ModuleCat.ofHom (X := ProdMN) (Y := M) (LinearMap.fst (R ⊗[k] Rᵐᵒᵖ) M N))).prod
    (tensorMap (k := k) X (ModuleCat.ofHom (X := ProdMN) (Y := N) (LinearMap.snd (R ⊗[k] Rᵐᵒᵖ) M N)))

def tensorProdInv : (EM × EN) →ₗ[R] EP :=
  (tensorMap (k := k) X (ModuleCat.ofHom (X := M) (Y := ProdMN) (LinearMap.inl (R ⊗[k] Rᵐᵒᵖ) M N))).coprod
    (tensorMap (k := k) X (ModuleCat.ofHom (X := N) (Y := ProdMN) (LinearMap.inr (R ⊗[k] Rᵐᵒᵖ) M N)))

@[simp] theorem tensorProdMap_tmul (m : EnvelopingBimodule k R ProdMN) (x : X) :
    tensorProdMap M N X (BalancedTensor.tmul (k := k) (R := R) m x) =
      (BalancedTensor.tmul (k := k) (R := R) (⟨m.value.1⟩ : EnvelopingBimodule k R M) x,
       BalancedTensor.tmul (k := k) (R := R) (⟨m.value.2⟩ : EnvelopingBimodule k R N) x) := rfl

theorem tensorProd_left (z : EP) : tensorProdInv M N X (tensorProdMap M N X z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul m x =>
    change BalancedTensor.tmul (k := k) (R := R) (⟨(m.value.1, 0)⟩ : EnvelopingBimodule k R ProdMN) x +
      BalancedTensor.tmul (k := k) (R := R) (⟨(0, m.value.2)⟩ : EnvelopingBimodule k R ProdMN) x = _
    rw [← BalancedTensor.add_tmul]
    congr 1
    apply EnvelopingBimodule.ext
    simp

theorem tensorProd_right (z : EM × EN) : tensorProdMap M N X (tensorProdInv M N X z) = z := by
  rcases z with ⟨z, w⟩
  have hz : tensorProdMap M N X (tensorProdInv M N X (z, 0)) = (z, 0) := by
    induction z using BalancedTensor.induction_on with
    | zero =>
      change tensorProdMap M N X (tensorProdInv M N X 0) = 0
      rw [(tensorProdInv M N X).map_zero, (tensorProdMap M N X).map_zero]
    | add z z' hz hz' =>
      have hh : (z+z', (0 : EN)) = (z, 0) + (z', 0) := by simp
      rw [hh, _root_.map_add, _root_.map_add, hz, hz']
    | tmul m x =>
      change tensorProdMap M N X
        (BalancedTensor.tmul (k := k) (R := R) (⟨(m.value, 0)⟩ : EnvelopingBimodule k R ProdMN) x + 0) = _
      rw [add_zero, tensorProdMap_tmul]
      simp
      exact BalancedTensor.zero_tmul _
  have hw : tensorProdMap M N X (tensorProdInv M N X (0, w)) = (0, w) := by
    induction w using BalancedTensor.induction_on with
    | zero =>
      change tensorProdMap M N X (tensorProdInv M N X 0) = 0
      rw [(tensorProdInv M N X).map_zero, (tensorProdMap M N X).map_zero]
    | add w w' hw hw' =>
      have hh : ((0 : EM), w+w') = (0, w) + (0, w') := by simp
      rw [hh, _root_.map_add, _root_.map_add, hw, hw']
    | tmul n x =>
      change tensorProdMap M N X
        (0 + BalancedTensor.tmul (k := k) (R := R) (⟨(0, n.value)⟩ : EnvelopingBimodule k R ProdMN) x) = _
      rw [zero_add, tensorProdMap_tmul]
      simp
      exact BalancedTensor.zero_tmul _
  have hh : (z, w) = (z, (0 : EN)) + (0, w) := by simp
  rw [hh, _root_.map_add, _root_.map_add, hz, hw]

def tensorProdEquiv : EP ≃ₗ[R] EM × EN where
  __ := tensorProdMap M N X
  invFun := tensorProdInv M N X
  left_inv := tensorProd_left M N X
  right_inv := tensorProd_right M N X

end ArExplicit.EnvelopingBimodule

end

end OAI
