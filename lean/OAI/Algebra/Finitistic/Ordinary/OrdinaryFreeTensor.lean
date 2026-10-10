import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorExactness
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Algebra.Opposite

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- A right-regular coefficient acts on the left tensor factor by its unop. -/
def coefficientAction : Aᵐᵒᵖ →ₗ[k] N →ₗ[k] N :=
  (Algebra.lsmul k k N).toLinearMap.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap

/-- Coordinate evaluation of a free right module tensor N. -/
def evaluateBilinear : (I →₀ Aᵐᵒᵖ) →ₗ[k] N →ₗ[k] (I →₀ N) :=
  Finsupp.lsum k (fun i => (coefficientAction (k := k) (A := A) N).compr₂ (Finsupp.lsingle i))

@[simp] theorem evaluateBilinear_single (i : I) (x : Aᵐᵒᵖ) (n : N) :
    evaluateBilinear (k := k) I N (Finsupp.single i x) n = Finsupp.single i (x.unop • n) := by
  simp only [evaluateBilinear,Finsupp.lsum_single]
  rfl

def evaluation : Tensor k A (I →₀ Aᵐᵒᵖ) N →ₗ[k] (I →₀ N) :=
  lift (evaluateBilinear (k := k) I N) (by
    intro a m n
    induction m using Finsupp.induction_linear with
    | zero => simp only [smul_zero,map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [smul_add,map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      rw [Finsupp.smul_single,evaluateBilinear_single,evaluateBilinear_single]
      change Finsupp.single i ((x.unop*a) • n) = Finsupp.single i (x.unop • (a • n))
      rw [mul_smul])

@[simp] theorem evaluation_single (i : I) (x : Aᵐᵒᵖ) (n : N) :
    evaluation (k := k) I N (mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i x) n) =
      Finsupp.single i (x.unop • n) := evaluateBilinear_single I N i x n

def insertion : (I →₀ N) →ₗ[k] Tensor k A (I →₀ Aᵐᵒᵖ) N :=
  Finsupp.lsum k (fun i => mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i 1))

omit [IsScalarTower k A N] in
@[simp] theorem insertion_single (i : I) (n : N) :
    insertion (k := k) (A := A) I N (Finsupp.single i n) =
      mk k A (I →₀ Aᵐᵒᵖ) N (Finsupp.single i 1) n := by
  simp only [insertion,Finsupp.lsum_single]

theorem evaluation_insertion (z : I →₀ N) :
    evaluation (k := k) (A := A) I N (insertion I N z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i n => rw [insertion_single,evaluation_single,MulOpposite.unop_one,one_smul]

theorem insertion_evaluation (z : Tensor k A (I →₀ Aᵐᵒᵖ) N) :
    insertion I N (evaluation (k := k) I N z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    induction m using Finsupp.induction_linear with
    | zero => simp only [map_zero,LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | single i x =>
      rw [evaluation_single,insertion_single,← balance]
      congr 1
      rw [MulOpposite.op_unop,Finsupp.smul_single,smul_eq_mul,mul_one]
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- The actual free balanced tensor, for arbitrary index sets and arbitrary modules N. -/
def equivalence : Tensor k A (I →₀ Aᵐᵒᵖ) N ≃ₗ[k] (I →₀ N) where
  __ := evaluation (k := k) I N
  invFun := insertion I N
  left_inv := insertion_evaluation I N
  right_inv := evaluation_insertion I N
end LittleFinitistic.BalancedTensor.Free

end

end OAI
