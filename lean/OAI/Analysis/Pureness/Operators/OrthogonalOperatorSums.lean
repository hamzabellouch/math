import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators
variable {B ι : Type*} [CStarAlgebra B] [Fintype ι]

lemma star_sum_mul_sum_of_orthogonal (x : ι → B)
    (hx : ∀ i j, i ≠ j → star (x i)*x j = 0) :
    star (∑ i, x i)*(∑ i, x i) = ∑ i, star (x i)*x i := by
  classical
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  exact Finset.sum_eq_single i (fun j _ hji => hx i j hji.symm) (by simp)

theorem norm_sum_le_sqrt_card (x : ι → B) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ i j, i ≠ j → star (x i)*x j = 0) (hb : ∀ i, ‖x i‖ ≤ C) :
    ‖∑ i, x i‖ ≤ Real.sqrt (Fintype.card ι) * C := by
  have hs : ‖∑ i, x i‖ ^ 2 ≤ (Fintype.card ι : ℝ)*C^2 := by
    calc
      _ = ‖star (∑ i, x i)*(∑ i, x i)‖ := by rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖∑ i, star (x i)*x i‖ := congrArg norm (star_sum_mul_sum_of_orthogonal x hx)
      _ ≤ ∑ i, ‖star (x i)*x i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, C^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [CStarRing.norm_star_mul_self, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) (hb i)
      _ = _ := by simp
  have hr : (Real.sqrt (Fintype.card ι)) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [norm_nonneg (∑ i, x i), Real.sqrt_nonneg (Fintype.card ι),
    mul_nonneg (Real.sqrt_nonneg (Fintype.card ι)) hC]

theorem norm_sum_le_sqrt_card_of_mul_star (x : ι → B) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ i j, i ≠ j → x i*star (x j) = 0) (hb : ∀ i, ‖x i‖ ≤ C) :
    ‖∑ i, x i‖ ≤ Real.sqrt (Fintype.card ι) * C := by
  have h := norm_sum_le_sqrt_card (fun i => star (x i)) C hC
    (fun i j hij => by simpa only [star_star] using hx i j hij)
    (fun i => by simpa only [norm_star] using hb i)
  simpa only [← star_sum, norm_star] using h
end CuntzPureness

end

end OAI
