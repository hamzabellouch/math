import Mathlib

namespace OAI

/-! # Global Lipschitz bounds from one ball and vanishing outside it -/

open Set Metric
open scoped NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem lipschitz_of_ball_and_zero (p : X) {R : ℝ} (hR : 0 ≤ R)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (closedBall p (R + 1)))
    (hz : ∀ x, R < dist p x → f x = 0) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  let B : ℝ := |f p| + (L : ℝ) * (R + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (x : X) : |f x| ≤ B := by
    by_cases hx : dist p x ≤ R
    · have hxp : x ∈ closedBall p (R + 1) := by
        rw [mem_closedBall, dist_comm]; linarith
      have hpp : p ∈ closedBall p (R + 1) := mem_closedBall_self (by linarith)
      have hh := (lipschitzOnWith_iff_dist_le_mul.mp hf) x hxp p hpp
      rw [Real.dist_eq, dist_comm x p] at hh
      have he := abs_add_le (f x - f p) (f p)
      rw [sub_add_cancel] at he
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_left hx L.coe_nonneg]
    · rw [hz x (lt_of_not_ge hx), abs_zero]
      exact hB
  let C : ℝ≥0 := max L ⟨B,hB⟩
  have hLC : (L : ℝ) ≤ C := by exact_mod_cast le_max_left L (⟨B,hB⟩ : ℝ≥0)
  have hBC : B ≤ C := by exact_mod_cast le_max_right L (⟨B,hB⟩ : ℝ≥0)
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hnear (a b : X) (ha : a ∈ closedBall p (R + 1))
      (hb : b ∈ closedBall p (R + 1)) : dist (f a) (f b) ≤ (C : ℝ) * dist a b :=
    ((lipschitzOnWith_iff_dist_le_mul.mp hf) a ha b hb).trans
      (mul_le_mul_of_nonneg_right hLC dist_nonneg)
  by_cases hx : x ∈ closedBall p (R + 1)
  · by_cases hy : y ∈ closedBall p (R + 1)
    · exact hnear x y hx hy
    · have hyp : R + 1 < dist p y := by simpa [mem_closedBall,dist_comm] using hy
      have hy0 := hz y (by linarith)
      by_cases hxR : dist p x ≤ R
      · have hxy : 1 ≤ dist x y := by linarith [dist_triangle p x y]
        rw [hy0,Real.dist_eq,sub_zero]
        exact (hb x).trans (hBC.trans (by nlinarith [C.coe_nonneg]))
      · rw [hz x (lt_of_not_ge hxR),hy0,dist_self]
        positivity
  · have hxp : R + 1 < dist p x := by simpa [mem_closedBall,dist_comm] using hx
    have hx0 := hz x (by linarith)
    by_cases hyR : dist p y ≤ R
    · have hxy : 1 ≤ dist x y := by
        have hh := dist_triangle p y x
        rw [dist_comm y x] at hh
        linarith
      rw [hx0,Real.dist_eq,zero_sub,abs_neg]
      exact (hb y).trans (hBC.trans (by nlinarith [C.coe_nonneg]))
    · rw [hx0,hz y (lt_of_not_ge hyR),dist_self]
      positivity

end RegularPointCoordinates

end OAI
