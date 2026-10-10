import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.ShortAverageGaussian
import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # The published Gaussian estimate gives the actual short-time average bound -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- Volume lower bounds are required only at the averaging ball and at
source points where the cutoff is nonzero. The constant precedes all radii. -/
theorem exists_cutoff_short_average_bound (hg : HasCoordinateHeatBounds μ ker)
    (n : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      ∀ (r t : ℝ) (x q : X), 0 < r → r ≤ 1 → 0 < t → t ≤ r ^ 2 →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ z, χ z * kernelAverage μ ker t (ball q r) z ≤
        C * r⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (36 * r ^ 2)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let Cg := (C₁ / V) * Real.exp C₂
  have hCg : 0 ≤ Cg := by dsimp only [Cg]; positivity
  obtain ⟨C, hC, hb⟩ := exists_short_average_gaussian μ hQ hk n hA hV hCg
    (by norm_num : (0 : ℝ) < 4 + 1 / 2)
  refine ⟨C, hC, ?_⟩
  intro χ hχ r t x q hr hr1 ht htr hfinite hvol hcenter hsource z
  have hnonneg : 0 ≤ kernelAverage μ ker t (ball q r) z :=
    (kernelAverage_bounds μ hQ hk ht (ball q r) z).1
  by_cases hz : χ z = 0
  · rw [hz, zero_mul]
    positivity
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have ht1 : t ≤ 1 := htr.trans (by nlinarith)
  have hv : 0 < V * (Real.sqrt t) ^ n := mul_pos hV (pow_pos hs n)
  have hvs := hsource z hz
  have hratio : C₁ / μ.real (ball z (Real.sqrt t)) ≤
      (C₁ / V) * (Real.sqrt t)⁻¹ ^ n := by
    have h := div_le_div_of_nonneg_left hC₁.le hv hvs
    simpa only [div_mul_eq_div_div, div_eq_mul_inv, inv_pow, mul_inv_rev, mul_assoc, mul_comm] using h
  have htime : Real.exp (C₂ * t) ≤ Real.exp C₂ := by
    apply Real.exp_le_exp.mpr
    nlinarith only [ht1, hC₂]
  have hkernel : ∀ y ∈ ball q r, ker t y z ≤
      Cg * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) := by
    intro y _
    have he := (hgauss t ht y z).2
    rw [Real.exp_add] at he
    have hm := mul_le_mul hratio htime (Real.exp_pos _).le
      (mul_nonneg (div_pos hC₁ hV).le (pow_nonneg (inv_pos.mpr hs).le n))
    calc
      _ ≤ (C₁ / μ.real (ball z (Real.sqrt t))) * Real.exp (C₂ * t) *
          Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) := by nlinarith only [he]
      _ ≤ ((C₁ / V) * (Real.sqrt t)⁻¹ ^ n) * Real.exp C₂ *
          Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by dsimp only [Cg]; ring
  have h := hb r t x q z hr ht htr hfinite hvol hcenter hkernel
  have hh := (mul_le_of_le_one_left hnonneg (hχ z).2).trans h
  norm_num at hh ⊢
  exact hh

end RegularPointCoordinates

end

end OAI
