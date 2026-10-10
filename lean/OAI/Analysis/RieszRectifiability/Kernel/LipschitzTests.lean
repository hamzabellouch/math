import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_const_mul_real {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) :
    LipschitzWith (‖c‖₊ * K) (fun x => c * f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (c * f x) (c * f y) = |c| * dist (f x) (f y) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    _ ≤ |c| * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg c)
    _ = ((‖c‖₊ * K : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]

theorem lipschitz_bounded_product_real {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  calc
    dist (f x * g x) (f y * g y) =
        |f x * (g x - g y) + (f x - f y) * g y| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using! abs_add_le
        (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * (Bg : ℝ) := by
      exact add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
        (mul_le_mul hf' (hBg y) (abs_nonneg _) (by positivity))
    _ = ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

variable [MeasurableSpace X]

theorem meanCorrection_lipschitz (μ : Measure X) {φ η : X → ℝ}
    {Kφ Kη : ℝ≥0} (hφ : LipschitzWith Kφ φ) (hη : LipschitzWith Kη η) :
    LipschitzWith (Kφ + ‖(∫ y, φ y ∂μ) / (∫ y, η y ∂μ)‖₊ * Kη)
      (meanCorrection μ φ η) :=
  hφ.sub (lipschitz_const_mul_real hη _)

theorem compactProjectedTest_lipschitz {d n : ℕ}
    (μ : Measure (Ambient d)) {χ : Ambient d → ℝ} {π : Ambient d → Ambient n}
    {φ : Ambient n → ℝ} {η : Ambient d → ℝ}
    {Kχ Kπ Kφ Kη Bχ Bφ : ℝ≥0}
    (hχ : LipschitzWith Kχ χ) (hπ : LipschitzWith Kπ π)
    (hφ : LipschitzWith Kφ φ) (hη : LipschitzWith Kη η)
    (hbχ : ∀ x, |χ x| ≤ (Bχ : ℝ)) (hbφ : ∀ y, |φ y| ≤ (Bφ : ℝ)) :
    LipschitzWith (Bχ * (Kφ * Kπ) + Kχ * Bφ +
      ‖(∫ y, χ y * φ (π y) ∂μ) / (∫ y, η y ∂μ)‖₊ * Kη)
      (compactProjectedTest μ χ π φ η) :=
  meanCorrection_lipschitz μ
    (lipschitz_bounded_product_real hχ (hφ.comp hπ) hbχ (fun x => hbφ (π x))) hη

end

end RieszRectifiability

end OAI
