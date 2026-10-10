import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedRepeat

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem signProduct_abs_le_one {α : Type*} (P U : Finset α) (hU : U ⊆ P)
    (y : α → ℤ) (hy : ∀ p ∈ P, y p = -1 ∨ y p = 0 ∨ y p = 1) :
    |∏ p ∈ U, (y p : ℝ)| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _p ∈ U, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro p hp
      rcases hy p (hU hp) with h | h | h <;> simp [h]
    _ = _ := by simp

theorem weighted_signProduct_summable {α Ω : Type*} (P U : Finset α) (hU : U ⊆ P)
    (w : Ω → ℝ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (y : Ω → α → ℤ) (hy : ∀ n p, p ∈ P → y n p = -1 ∨ y n p = 0 ∨ y n p = 1) :
    Summable (fun n => w n * ∏ p ∈ U, (y n p : ℝ)) := by
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
  exact mul_le_of_le_one_right (hw n) (signProduct_abs_le_one P U hU (y n) (hy n))

theorem integrated_distinctSignAverage {α Ω : Type*} [DecidableEq α]
    (P : Finset α) (w : Ω → ℝ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (y : Ω → α → ℤ) (hy : ∀ n p, p ∈ P → y n p = -1 ∨ y n p = 0 ∨ y n p = 1)
    (k : ℕ) :
    (∑' n, w n * distinctSignAverage P (y n) k) =
      ((k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ∑ U ∈ P.powersetCard k, ∑' n, w n * ∏ p ∈ U, (y n p : ℝ) := by
  have hf (n : Ω) : w n * distinctSignAverage P (y n) k =
      ((k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ∑ U ∈ P.powersetCard k, w n * ∏ p ∈ U, (y n p : ℝ) := by
    unfold distinctSignAverage
    rw [← Finset.mul_sum]
    ring
  simp_rw [hf]
  rw [tsum_mul_left]
  congr 1
  exact Summable.tsum_finsetSum (fun U hU => weighted_signProduct_summable P U
    (Finset.mem_powersetCard.mp hU).1 w hw hs y hy)

theorem integrated_distinct_le_sum_abs {α Ω : Type*} [DecidableEq α]
    (P : Finset α) (w : Ω → ℝ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (y : Ω → α → ℤ) (hy : ∀ n p, p ∈ P → y n p = -1 ∨ y n p = 0 ∨ y n p = 1)
    (k : ℕ) :
    (∑' n, w n * distinctSignAverage P (y n) k) ≤
      ((k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ∑ U ∈ P.powersetCard k, |∑' n, w n * ∏ p ∈ U, (y n p : ℝ)| := by
  rw [integrated_distinctSignAverage P w hw hs y hy k]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun U hU => le_abs_self _)

end Ostmann.QuadraticCenter

end

end OAI
