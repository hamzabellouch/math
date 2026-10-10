import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

abbrev regularObject : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (R ⊗[k] Rᵐᵒᵖ)

private def unopAction : Rᵐᵒᵖ →ₗ[k] X →ₗ[k] X where
  toFun b :=
    { toFun := fun x => b.unop • x
      map_add' := smul_add b.unop
      map_smul' := by intros; exact smul_comm _ _ _ }
  map_add' b c := by ext x; exact add_smul b.unop c.unop x
  map_smul' c b := by
    ext x
    change (c • b.unop) • x = c • (b.unop • x)
    exact smul_assoc c b.unop x

private def regularRaw : (R ⊗[k] Rᵐᵒᵖ) →ₗ[k] X →ₗ[k] (R ⊗[k] X) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => (TensorProduct.mk k R X a).comp (unopAction k R X b)
          map_add' := by intros; ext x; simp [unopAction, add_smul, TensorProduct.tmul_add]
          map_smul' := by intros; ext x; simp [unopAction] }
      map_add' := by intros; ext b x; simp
      map_smul' := by intros; ext b x; simp }

@[simp] private theorem regularRaw_tmul (a : R) (b : Rᵐᵒᵖ) (x : X) :
    regularRaw k R X (a ⊗ₜ[k] b) x = a ⊗ₜ[k] (b.unop • x) := rfl

private def regularBilinear : EnvelopingBimodule k R (regularObject k R) →ₗ[k]
    X →ₗ[k] (R ⊗[k] X) :=
  (regularRaw k R X).comp (scalarEquiv (regularObject k R)).toLinearMap

private theorem regularBilinear_balance
    (f : EnvelopingBimodule k R (regularObject k R)) (r : R) (x : X) :
    regularBilinear k R X (MulOpposite.op r • f) x =
      regularBilinear k R X f (r • x) := by
  rcases f with ⟨f⟩
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    change regularRaw k R X (((1 : R) ⊗ₜ[k] MulOpposite.op r) * (f + g)) x =
      regularRaw k R X (f + g) (r • x)
    simp only [mul_add, _root_.map_add, LinearMap.add_apply] at *
    exact congrArg₂ (· + ·) hf hg
  | tmul a b =>
    change regularRaw k R X (((1 : R) ⊗ₜ[k] MulOpposite.op r) * (a ⊗ₜ[k] b)) x =
      regularRaw k R X (a ⊗ₜ[k] b) (r • x)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, regularRaw_tmul,
      MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul]

private theorem regularBilinear_left
    (r : R) (f : EnvelopingBimodule k R (regularObject k R)) (x : X) :
    regularBilinear k R X (r • f) x = r • regularBilinear k R X f x := by
  rcases f with ⟨f⟩
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    change regularRaw k R X ((r ⊗ₜ[k] (1 : Rᵐᵒᵖ)) * (f + g)) x =
      r • regularRaw k R X (f + g) x
    simp only [mul_add, _root_.map_add, LinearMap.add_apply, smul_add] at *
    exact congrArg₂ (· + ·) hf hg
  | tmul a b =>
    change regularRaw k R X ((r ⊗ₜ[k] (1 : Rᵐᵒᵖ)) * (a ⊗ₜ[k] b)) x =
      r • regularRaw k R X (a ⊗ₜ[k] b) x
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, regularRaw_tmul,
      TensorProduct.smul_tmul', smul_eq_mul]

def regularEvaluation :
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X →ₗ[R]
      R ⊗[k] X :=
  BalancedTensor.liftLeft (regularBilinear k R X)
    (regularBilinear_balance k R X) (regularBilinear_left k R X)

@[simp] theorem regularEvaluation_tmul (a : R) (b : Rᵐᵒᵖ) (x : X) :
    regularEvaluation k R X (BalancedTensor.tmul ⟨a ⊗ₜ[k] b⟩ x) =
      a ⊗ₜ[k] (b.unop • x) := rfl

private def regularInclusion : R →ₗ[k] EnvelopingBimodule k R (regularObject k R) where
  toFun a := ⟨a ⊗ₜ[k] (1 : Rᵐᵒᵖ)⟩
  map_add' a b := by ext; exact TensorProduct.add_tmul a b 1
  map_smul' c a := by ext; exact TensorProduct.smul_tmul' c a 1

private def regularInverse : R ⊗[k] X →ₗ[k]
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X :=
  TensorProduct.lift ((BalancedTensor.mk (k := k) (R := R)).comp (regularInclusion k R))

omit [IsScalarTower k R X] in
@[simp] private theorem regularInverse_tmul (a : R) (x : X) :
    regularInverse k R X (a ⊗ₜ[k] x) =
      BalancedTensor.tmul (⟨a ⊗ₜ[k] (1 : Rᵐᵒᵖ)⟩ : EnvelopingBimodule k R (regularObject k R)) x := rfl

private theorem regularInverse_evaluation
    (z : BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X) :
    regularInverse k R X (regularEvaluation k R X z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [_root_.map_zero]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul f x =>
    rcases f with ⟨f⟩
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      change regularInverse k R X (regularEvaluation k R X
        (BalancedTensor.tmul ((⟨f⟩ : EnvelopingBimodule k R (regularObject k R)) + ⟨g⟩) x)) =
          BalancedTensor.tmul ((⟨f⟩ : EnvelopingBimodule k R (regularObject k R)) + ⟨g⟩) x
      simpa only [BalancedTensor.add_tmul, _root_.map_add] using congrArg₂ (· + ·) hf hg
    | tmul a b =>
      rw [regularEvaluation_tmul, regularInverse_tmul, ← BalancedTensor.balance]
      congr 1
      apply EnvelopingBimodule.ext
      change (((1 : R) ⊗ₜ[k] MulOpposite.op b.unop) * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ))) = a ⊗ₜ[k] b
      simp only [MulOpposite.op_unop, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem regularEvaluation_inverse (z : R ⊗[k] X) :
    regularEvaluation k R X (regularInverse k R X z) = z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul a x => simp only [regularInverse_tmul, regularEvaluation_tmul, MulOpposite.unop_one, one_smul]

def regularEquiv :
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X ≃ₗ[R] R ⊗[k] X where
  __ := regularEvaluation k R X
  invFun := regularInverse k R X
  left_inv := regularInverse_evaluation k R X
  right_inv := regularEvaluation_inverse k R X

end ArExplicit.EnvelopingBimodule

end

end OAI
