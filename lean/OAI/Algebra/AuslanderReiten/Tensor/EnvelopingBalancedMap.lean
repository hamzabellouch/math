import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBimodule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

def map (f : M ⟶ N) : EnvelopingBimodule k R M →ₗ[k] EnvelopingBimodule k R N where
  toFun x := ⟨f.hom x.value⟩
  map_add' x y := by
    ext
    exact f.hom.map_add x.value y.value
  map_smul' c x := by
    ext
    exact (f.hom.restrictScalars k).map_smul c x.value

@[simp] theorem map_value (f : M ⟶ N) (x : EnvelopingBimodule k R M) :
    (map f x).value = f.hom x.value := rfl

@[simp] theorem map_left_smul (f : M ⟶ N) (a : R)
    (x : EnvelopingBimodule k R M) : map f (a • x) = a • map f x := by
  ext
  exact f.hom.map_smul (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x.value

@[simp] theorem map_right_smul (f : M ⟶ N) (b : Rᵐᵒᵖ)
    (x : EnvelopingBimodule k R M) : map f (b • x) = b • map f x := by
  ext
  exact f.hom.map_smul ((1 : R) ⊗ₜ[k] b) x.value

def mapLeft (f : M ⟶ N) : EnvelopingBimodule k R M →ₗ[R] EnvelopingBimodule k R N where
  toFun := map f
  map_add' := (map f).map_add
  map_smul' := map_left_smul f

@[simp] theorem map_id : map (𝟙 M) = LinearMap.id := by
  ext x
  rfl

@[simp] theorem map_comp (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = (map g).comp (map f) := by
  ext x
  rfl

@[simp] theorem map_zero : map (0 : M ⟶ N) = 0 := by
  ext x
  rfl

@[simp] theorem map_add (f g : M ⟶ N) : map (f + g) = map f + map g := by
  ext x
  rfl

variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

def tensorMap (f : M ⟶ N) :
    BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R N) X where
  __ := (BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
    (map_right_smul f) (fun _ _ => rfl)).toAddHom
  map_smul' a z := by
    change BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
      (map_right_smul f) (fun _ _ => rfl) (a • z) =
        a • BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
          (map_right_smul f) (fun _ _ => rfl) z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | tmul m x => simp only [BalancedTensor.smul_tmul, BalancedTensor.map_tmul,
        LinearMap.id_apply, map_left_smul]
    | add z w hz hw => simp_all

omit [IsScalarTower k R X]

@[simp] theorem tensorMap_tmul (f : M ⟶ N)
    (m : EnvelopingBimodule k R M) (x : X) :
    tensorMap X f (BalancedTensor.tmul m x) = BalancedTensor.tmul (map f m) x := rfl

@[simp] theorem tensorMap_id : tensorMap X (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => rfl
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    tensorMap X (f ≫ g) = (tensorMap X g).comp (tensorMap X f) := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => rfl
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_zero : tensorMap X (0 : M ⟶ N) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => simp
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_add (f g : M ⟶ N) :
    tensorMap X (f + g) = tensorMap X f + tensorMap X g := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => simp [BalancedTensor.add_tmul]
  | add z w hz hw =>
    simp only [_root_.LinearMap.map_add, hz, hw]

end ArExplicit.EnvelopingBimodule

end

end OAI
