import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.UncenteredEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_product_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0) (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, f x ≠ 0 → |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  by_cases hy : f y = 0
  · by_cases hx : f x = 0
    · simp only [hx, hy, zero_mul, dist_self]
      positivity
    · calc
        dist (f x * g x) (f y * g y) = |f x - f y| * |g x| := by
          simp only [hy, zero_mul, Real.dist_eq, sub_zero, abs_mul]
        _ ≤ ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
          mul_le_mul hf' (hBg x hx) (abs_nonneg _) (by positivity)
        _ ≤ ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          nlinarith [mul_nonneg (mul_nonneg Bf.coe_nonneg Kg.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · calc
      dist (f x * g x) (f y * g y) = |f x * (g x - g y) + (f x - f y) * g y| := by
        rw [Real.dist_eq]
        congr 1
        ring
      _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
        simpa only [abs_mul] using! abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
        add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
          (mul_le_mul hf' (hBg y hy) (abs_nonneg _) (by positivity))
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

theorem squared_cutoff_height_globally_lipschitz {X : Type*} [PseudoMetricSpace X]
    (w χ : X → ℝ) (K L W : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hbound : ∀ x, |χ x| ≤ 1) (hW : ∀ x, χ x ≠ 0 → |w x| ≤ (W : ℝ)) :
    LipschitzWith (K + 2 * L * W) (fun x => χ x ^ 2 * w x) := by
  have hsquare : LipschitzWith (1 * L + L * 1) (fun x => χ x ^ 2) := by
    simpa only [pow_two] using! lipschitz_bounded_product_real (Bf := 1) (Bg := 1) hχ hχ hbound hbound
  have h := lipschitz_product_of_bound_on_support (fun x => χ x ^ 2) w (1 * L + L * 1) K 1 W
    hsquare hw
    (fun x => by
      rw [abs_of_nonneg (sq_nonneg (χ x))]
      exact cutoff_square_le_one χ hbound x)
    (fun x hx => hW x (fun hz => hx (by simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)])))
  convert! h using 1
  ring

theorem squared_cutoff_height_hasCompactSupport {d : ℕ}
    (w χ : Ambient d → ℝ) (a : Ambient d) (H : ℝ)
    (hsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H) :
    HasCompactSupport (fun x => χ x ^ 2 * w x) := by
  apply HasCompactSupport.intro (isCompact_closedBall a H)
  intro x hx
  have hz : χ x = 0 := by
    by_contra hn
    exact hx (hsupport x hn)
  simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]

theorem squared_cutoff_mean_zero_global {d : ℕ}
    (μ : Measure (Ambient d)) (w χ : Ambient d → ℝ) (a : Ambient d) (H R : ℝ)
    (hHR : H < R) (hsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0) :
    (∫ x, χ x ^ 2 * w x ∂μ) = 0 := by
  have heq : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = ∫ x, χ x ^ 2 * w x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := by
      by_contra hn
      exact hx ((hsupport x hn).trans_lt hHR)
    simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  exact heq.symm.trans hzero

end

end RieszRectifiability

end OAI
