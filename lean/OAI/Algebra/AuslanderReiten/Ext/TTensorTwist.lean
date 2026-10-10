import OAI.Algebra.AuslanderReiten.Ext.TTwistExtPolynomial
import OAI.Algebra.AuslanderReiten.Ext.TTensorPolynomial

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tTensorInverseTwist (n : ℕ) : tTensorCoefficients q n →ₗ[k] tTensorCoefficients q n where
  toFun x p := TensorProduct.map (tInverseTwistExt q H p.val.1)
    (tInverseTwistExt q H p.val.2) (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' a x := by
    funext p
    exact (TensorProduct.map (tInverseTwistExt q H p.val.1)
      (tInverseTwistExt q H p.val.2)).map_smul a (x p)

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem tTensorInverseTwist_apply (n : ℕ) (x : tTensorCoefficients q n)
    (p : ExternalTensor.Diagonal n) :
    tTensorInverseTwist q H n x p = TensorProduct.map
      (tInverseTwistExt q H p.val.1) (tInverseTwistExt q H p.val.2) (x p) := rfl

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
include hq hq1 hp

theorem tInverseTwist_tensor_scalar (a b : ℕ)
    (x : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    TensorProduct.map (tInverseTwistExt q H (3*a)) (tInverseTwistExt q H (3*b)) x =
      (((H⁻¹ : kˣ) : k)^(a+b)) • x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x y =>
    rw [TensorProduct.map_tmul, tInverseTwistExt_all q H hq hq1 hp,
      tInverseTwistExt_all q H hq hq1 hp, TensorProduct.smul_tmul_smul, pow_add]

theorem tTensorInverseTwist_diagonal (n : ℕ) (i : Fin (n+1))
    (x : tTensorCoefficients q (3*n)) :
    tTensorInverseTwist q H (3*n) x (polynomialDiagonal n i) =
      (((H⁻¹ : kˣ) : k)^n) • x (polynomialDiagonal n i) := by
  have h := tInverseTwist_tensor_scalar q H hq hq1 hp i.val (n-i.val)
    (x (polynomialDiagonal n i))
  have hi : i.val + (n-i.val) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)
  rw [hi] at h
  rw [tTensorInverseTwist_apply]
  dsimp only [polynomialDiagonal]
  dsimp only [polynomialDiagonal] at h
  exact h

theorem tTensorInverseTwist_scalar (n : ℕ) (x : tTensorCoefficients q (3*n)) :
    tTensorInverseTwist q H (3*n) x = (((H⁻¹ : kˣ) : k)^n) • x := by
  classical
  funext p
  by_cases hi : ∃ i, polynomialDiagonal n i=p
  · obtain ⟨i,rfl⟩ := hi
    exact tTensorInverseTwist_diagonal q H hq hq1 hp n i x
  · have hx := tTensorCoefficient_off_diagonal q hq hq1 hp n p hi (x p)
    rw [tTensorInverseTwist_apply]
    simp only [Pi.smul_apply, hx, map_zero, smul_zero]

end ArExplicit.Resolution

end

end OAI
