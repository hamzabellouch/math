import OAI.Analysis.Pureness.Operators.OrthogonalOperatorSums
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators
variable {B ι : Type*} [CStarAlgebra B] [Fintype ι]

theorem powers_projection_sum_bound (p x : ι → B) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ i, star (p i) = p i) (ho : ∀ i j, i ≠ j → p i*p j = 0)
    (hn : ∀ i, ‖p i‖ ≤ 1) (hcn : ∀ i, ‖1-p i‖ ≤ 1)
    (hx : ∀ i, ‖x i‖ ≤ C) (hz : ∀ i, (1-p i)*x i*(1-p i) = 0) :
    ‖∑ i, x i‖ ≤ 2*Real.sqrt (Fintype.card ι)*C := by
  let a := fun i => p i*x i
  let b := fun i => (1-p i)*x i*p i
  have he (i : ι) : x i = a i+b i := by
    calc
      x i = a i+b i+(1-p i)*x i*(1-p i) := by dsimp [a,b]; noncomm_ring
      _ = a i+b i := by rw [hz i, add_zero]
  have ha : ‖∑ i, a i‖ ≤ Real.sqrt (Fintype.card ι)*C := by
    apply norm_sum_le_sqrt_card a C hC
    · intro i j hij
      dsimp [a]
      rw [star_mul, hp i]
      calc
        _ = star (x i)*(p i*p j)*x j := by simp only [mul_assoc]
        _ = 0 := by rw [ho i j hij, mul_zero, zero_mul]
    · intro i
      exact (norm_mul_le _ _).trans ((mul_le_mul (hn i) (hx i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hb : ‖∑ i, b i‖ ≤ Real.sqrt (Fintype.card ι)*C := by
    apply norm_sum_le_sqrt_card_of_mul_star b C hC
    · intro i j hij
      dsimp [b]
      simp only [star_mul, hp j]
      calc
        _ = ((1-p i)*x i)*(p i*p j)*(star (x j)*star (1-p j)) := by simp only [mul_assoc]
        _ = 0 := by rw [ho i j hij, mul_zero, zero_mul]
    · intro i
      dsimp [b]
      calc
        _ ≤ (‖1-p i‖*‖x i‖)*‖p i‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (1*C)*1 := by gcongr; exact hcn i; exact hx i; exact hn i
        _ = C := by ring
  calc
    _ = ‖(∑ i, a i)+(∑ i, b i)‖ := by simp only [he, Finset.sum_add_distrib]
    _ ≤ ‖∑ i, a i‖+‖∑ i, b i‖ := norm_add_le _ _
    _ ≤ 2*Real.sqrt (Fintype.card ι)*C := by linarith
end CuntzPureness

end

end OAI
