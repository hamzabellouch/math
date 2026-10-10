import OAI.Algebra.AuslanderReiten.Bar.BarBalancedRaw
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBimodule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

abbrev bar (n : ℕ) := EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)
abbrev evaluated (n : ℕ) := BalancedTensor k R (bar k R n) M

def coordinates (n : ℕ) : bar k R n ≃ₗ[k] AbsoluteBar.object k R n :=
  EnvelopingBimodule.scalarEquiv (AbsoluteBar.moduleObject k R n)

theorem coordinates_left (n : ℕ) (a : R) (x : bar k R n) :
    coordinates k R n (a • x) = AbsoluteBar.left k R n a (coordinates k R n x) := by
  change AbsoluteBar.left k R n a (AbsoluteBar.right k R n 1 x.value) =
    AbsoluteBar.left k R n a x.value
  rw [map_one]
  rfl

theorem coordinates_right (n : ℕ) (a : Rᵐᵒᵖ) (x : bar k R n) :
    coordinates k R n (a • x) = AbsoluteBar.right k R n a (coordinates k R n x) := by
  change AbsoluteBar.left k R n 1 (AbsoluteBar.right k R n a x.value) =
    AbsoluteBar.right k R n a x.value
  exact AbsoluteBar.left_one k R n _

def evalBilinear (n : ℕ) : bar k R n →ₗ[k] M →ₗ[k] ModuleBar.moduleObject k R M n where
  toFun x := (rawEval k R M n).comp (TensorProduct.mk k (AbsoluteBar.object k R n) M
    (coordinates k R n x))
  map_add' x y := by
    ext m
    change rawEval k R M n (coordinates k R n (x+y) ⊗ₜ[k] m) =
      rawEval k R M n (coordinates k R n x ⊗ₜ[k] m) + rawEval k R M n (coordinates k R n y ⊗ₜ[k] m)
    rw [map_add, TensorProduct.add_tmul, map_add]
  map_smul' a x := by
    ext m
    change rawEval k R M n (coordinates k R n (a • x) ⊗ₜ[k] m) =
      a • rawEval k R M n (coordinates k R n x ⊗ₜ[k] m)
    rw [map_smul]
    exact (congrArg (rawEval k R M n)
      (TensorProduct.smul_tmul' a (coordinates k R n x) m).symm).trans
      ((rawEval k R M n).map_smul a (coordinates k R n x ⊗ₜ[k] m))

@[simp] theorem evalBilinear_apply (n : ℕ) (x : bar k R n) (m : M) :
    evalBilinear k R M n x m = rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

theorem evalBilinear_balance (n : ℕ) (x : bar k R n) (a : R) (m : M) :
    evalBilinear k R M n (MulOpposite.op a • x) m = evalBilinear k R M n x (a • m) := by
  rw [evalBilinear_apply, coordinates_right, evalBilinear_apply]
  exact rawEval_right k R M n (MulOpposite.op a) _ m

theorem evalBilinear_left (n : ℕ) (a : R) (x : bar k R n) (m : M) :
    evalBilinear k R M n (a • x) m = a • evalBilinear k R M n x m := by
  rw [evalBilinear_apply, coordinates_left]
  exact rawEval_left k R M n a _ m

def evaluation (n : ℕ) : evaluated k R M n →ₗ[R] ModuleBar.moduleObject k R M n :=
  BalancedTensor.liftLeft (evalBilinear k R M n) (evalBilinear_balance k R M n)
    (evalBilinear_left k R M n)

@[simp] theorem evaluation_tmul (n : ℕ) (x : bar k R n) (m : M) :
    evaluation k R M n (BalancedTensor.tmul x m) =
      rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

def prepend (n : ℕ) (a : R) : bar k R n →ₗ[k] bar k R (n+1) :=
  (coordinates k R (n+1)).symm.toLinearMap.comp
    ((TensorProduct.mk k R (AbsoluteBar.object k R n) a).comp
      (coordinates k R n).toLinearMap)

@[simp] theorem coordinates_prepend (n : ℕ) (a : R) (x : bar k R n) :
    coordinates k R (n+1) (prepend k R n a x) = a ⊗ₜ[k] coordinates k R n x :=
  (coordinates k R (n+1)).apply_symm_apply _

theorem prepend_right (n : ℕ) (a : R) (b : Rᵐᵒᵖ) (x : bar k R n) :
    prepend k R n a (b • x) = b • prepend k R n a x := by
  apply (coordinates k R (n+1)).injective
  rw [coordinates_prepend, coordinates_right, coordinates_right,
    coordinates_prepend, AbsoluteBar.right_tmul]

def prependBalanced (n : ℕ) (a : R) : evaluated k R M n →ₗ[k] evaluated k R M (n+1) :=
  BalancedTensor.map (prepend k R n a) LinearMap.id (prepend_right k R n a) (by intros; rfl)

omit [IsScalarTower k R M] in
@[simp] theorem prependBalanced_tmul (n : ℕ) (a : R) (x : bar k R n) (m : M) :
    prependBalanced k R M n a (BalancedTensor.tmul x m) =
      BalancedTensor.tmul (prepend k R n a x) m := rfl

def cons (n : ℕ) : R →ₗ[k] evaluated k R M n →ₗ[k] evaluated k R M (n+1) where
  toFun := prependBalanced k R M n
  map_add' a b := by
    apply BalancedTensor.hom_ext
    intro x m
    simp only [LinearMap.add_apply, prependBalanced_tmul]
    rw [← BalancedTensor.add_tmul (k := k) (R := R)]
    congr 1
    apply (coordinates k R (n+1)).injective
    rw [map_add, coordinates_prepend k R n (a+b) x,
      coordinates_prepend k R n a x, coordinates_prepend k R n b x, TensorProduct.add_tmul]
  map_smul' c a := by
    apply BalancedTensor.hom_ext
    intro x m
    simp only [RingHom.id_apply, LinearMap.smul_apply, prependBalanced_tmul]
    rw [← BalancedTensor.scalar_tmul (k := k) (R := R)]
    congr 1

end ArExplicit.BarBalanced

end

end OAI
