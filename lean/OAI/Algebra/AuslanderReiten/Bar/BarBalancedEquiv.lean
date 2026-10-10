import OAI.Algebra.AuslanderReiten.Bar.BarBalancedModule

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

def embedding : (n : ℕ) → ModuleBar.object k R M n →ₗ[k] evaluated k R M n
  | 0 => BalancedTensor.mk ((coordinates k R 0).symm 1)
  | n+1 => TensorProduct.lift ((LinearMap.lcomp k _ (embedding n)).comp (cons k R M n))

omit [IsScalarTower k R M] in
@[simp] theorem embedding_succ (n : ℕ) (a : R) (x : ModuleBar.object k R M n) :
    embedding k R M (n+1) (a ⊗ₜ[k] x) =
      prependBalanced k R M n a (embedding k R M n x) := rfl

theorem evaluation_prepend (n : ℕ) (a : R) (z : evaluated k R M n) :
    evaluation k R M (n+1) (prependBalanced k R M n a z) =
      a ⊗ₜ[k] evaluation k R M n z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp; rfl
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]; rfl
  | tmul x m =>
    rw [prependBalanced_tmul, evaluation_tmul, coordinates_prepend,
      rawEval_succ, evaluation_tmul]
    rfl

theorem evaluation_embedding (n : ℕ) (x : ModuleBar.object k R M n) :
    evaluation k R M n (embedding k R M n x) = x := by
  induction n with
  | zero =>
    change rawEval k R M 0 (((coordinates k R 0) ((coordinates k R 0).symm 1)) ⊗ₜ[k] x) = x
    rw [LinearEquiv.apply_symm_apply, rawEval_zero, one_smul]
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul a x => rw [embedding_succ, evaluation_prepend, ih]; rfl

theorem embedding_rawEval (n : ℕ) (x : AbsoluteBar.object k R n) (m : M) :
    embedding k R M n (rawEval k R M n (x ⊗ₜ[k] m)) =
      BalancedTensor.tmul ((coordinates k R n).symm x) m := by
  induction n with
  | zero =>
    change BalancedTensor.tmul ((coordinates k R 0).symm 1) (x • m) = _
    rw [← BalancedTensor.balance]
    congr 1
    apply (coordinates k R 0).injective
    rw [coordinates_right, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact one_mul x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, hx, hy, BalancedTensor.add_tmul]
    | tmul a x =>
      rw [rawEval_succ, embedding_succ, ih, prependBalanced_tmul]
      congr 1

theorem embedding_evaluation (n : ℕ) (z : evaluated k R M n) :
    embedding k R M n (evaluation k R M n z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero =>
    rw [(evaluation k R M n).map_zero]
    exact (embedding k R M n).map_zero
  | add x y hx hy =>
    rw [(evaluation k R M n).map_add]
    exact ((embedding k R M n).map_add _ _).trans (congrArg₂ (· + ·) hx hy)
  | tmul x m =>
    rw [evaluation_tmul, embedding_rawEval, LinearEquiv.symm_apply_apply]

def equiv (n : ℕ) : evaluated k R M n ≃ₗ[R] ModuleBar.moduleObject k R M n :=
  LinearEquiv.ofBijective (evaluation k R M n) ⟨
    fun _ _ h => (embedding_evaluation k R M n _).symm.trans
      ((congrArg (embedding k R M n) h).trans (embedding_evaluation k R M n _)),
    fun x => ⟨embedding k R M n x, evaluation_embedding k R M n x⟩⟩

@[simp] theorem equiv_tmul (n : ℕ) (x : bar k R n) (m : M) :
    equiv k R M n (BalancedTensor.tmul x m) =
      rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

end ArExplicit.BarBalanced

end

end OAI
