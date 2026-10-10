import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.LongAverageGaussian
import OAI.Geometry.RCD.Heat.AveragedKernelDifference

namespace OAI

/-! # The averaged kernel difference on every time above the ball scale -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem gaussian_denominator_mono {d t D E : ℝ}
    (ht : 0 < t) (hD : 0 < D) (hDE : D ≤ E) :
    Real.exp (-d ^ 2 / (D * t)) ≤ Real.exp (-d ^ 2 / (E * t)) := by
  have h := div_le_div_of_nonneg_left (sq_nonneg d) (mul_pos hD ht)
    (mul_le_mul_of_nonneg_right hDE ht.le)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg h

private theorem inverse_volume_power {v s V C : ℝ} {n : ℕ}
    (hs : 0 < s) (hV : 0 < V) (hC : 0 ≤ C) (hvol : V * s ^ n ≤ v) :
    C / v ≤ (C / V) * s⁻¹ ^ n := by
  have h := div_le_div_of_nonneg_left hC (mul_pos hV (pow_pos hs n)) hvol
  simpa only [div_mul_eq_div_div, div_eq_mul_inv, inv_pow, mul_inv_rev, mul_assoc, mul_comm] using h

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The Gaussian gradient input controls long times; the ordinary
Gaussian bound handles the finite transition interval just above r². -/
theorem exists_long_average_difference_bound
    (hg : HasCoordinateHeatBounds μ ker) (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (r t : ℝ) (x q z : X),
      0 < r → 0 < t → t ≤ 1 → r ^ 2 ≤ t →
      μ (ball q r) ≠ ∞ → 0 < μ.real (ball q r) → dist x q ≤ A * r →
      V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t)) →
      |kernelAverage μ ker t (ball q r) z - ker t x z| ≤
        C * r * (Real.sqrt t)⁻¹ ^ (n + 1) * Real.exp (-(dist x z) ^ 2 / (D * t)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cg, Dg, Bg, hCg, hDg, hBg, hgradient⟩ := hdiff
  let D := max 9 Dg
  let P := (C₁ / V) * Real.exp C₂
  let M := P * (Real.exp ((A + 1) ^ 2 / (4 + 1 / 2)) + 1)
  let L := (Cg / V) * (A + 1) * Real.exp Bg
  let C := L + M * (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hD : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9) (le_max_left _ _)
  refine ⟨C, D, hC, hD, ?_⟩
  intro r t x q z hr ht ht1 hrt hfinite hvol hcenter hsource
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hpow : 0 ≤ (Real.sqrt t)⁻¹ ^ n := by positivity
  have hcoef := inverse_volume_power hs hV hC₁.le hsource
  have htime : Real.exp (C₂ * t) ≤ Real.exp C₂ := by
    apply Real.exp_le_exp.mpr
    nlinarith only [ht1, hC₂]
  have hpoint (y : X) : ker t y z ≤
      P * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) := by
    have hu := (hgauss t ht y z).2
    rw [Real.exp_add] at hu
    have hm := mul_le_mul hcoef htime (Real.exp_pos _).le
      (mul_nonneg (div_pos hC₁ hV).le hpow)
    calc
      _ ≤ (C₁ / μ.real (ball z (Real.sqrt t))) * Real.exp (C₂ * t) *
          Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) := by nlinarith only [hu]
      _ ≤ ((C₁ / V) * (Real.sqrt t)⁻¹ ^ n) * Real.exp C₂ *
          Real.exp (-(dist y z) ^ 2 / ((4 + 1 / 2) * t)) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by dsimp only [P]; ring
  by_cases hscale : (A + 1) * r ≤ Real.sqrt t
  · have hraw := averaged_kernel_difference_bound μ hQ hk hCg.le hgradient ht ht1 hr
      x q z hfinite hvol hcenter hscale
    have hratio := inverse_volume_power hs hV hCg.le hsource
    have hc : Cg / (Real.sqrt t * μ.real (ball z (Real.sqrt t))) ≤
        (Cg / V) * (Real.sqrt t)⁻¹ ^ (n + 1) := by
      have hh := mul_le_mul_of_nonneg_left hratio (inv_pos.mpr hs).le
      simpa only [div_eq_mul_inv, mul_inv_rev, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
    have hgrow : Real.exp (Bg * t) ≤ Real.exp Bg := by
      apply Real.exp_le_exp.mpr
      nlinarith only [ht1, hBg]
    have hdecay := gaussian_denominator_mono (d := dist x z) ht hDg (le_max_right 9 Dg)
    rw [Real.exp_add] at hraw
    calc
      _ ≤ ((Cg / V) * (Real.sqrt t)⁻¹ ^ (n + 1)) * ((A + 1) * r) *
          (Real.exp (-(dist x z) ^ 2 / (D * t)) * Real.exp Bg) := by
        apply hraw.trans
        gcongr
      _ = L * r * (Real.sqrt t)⁻¹ ^ (n + 1) * Real.exp (-(dist x z) ^ 2 / (D * t)) := by
        dsimp only [L]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hr.le
        dsimp only [C]
        exact le_add_of_nonneg_right (by positivity)
  · have havg := kernelAverage_gaussian_above_scale μ hQ hk hr ht hA
      (mul_nonneg hP.le hpow) (by norm_num : (0 : ℝ) < 4 + 1 / 2)
      hrt x q z hfinite hvol hcenter (fun y _ => hpoint y)
    have hdecay := gaussian_denominator_mono (d := dist x z) ht
      (by norm_num : (0 : ℝ) < 9) (le_max_left 9 Dg)
    have hdecay' := gaussian_denominator_mono (d := dist x z) ht
      (by norm_num : (0 : ℝ) < 4 + 1 / 2)
      (show 4 + (1 / 2 : ℝ) ≤ D by dsimp only [D]; exact (by norm_num : (4 + (1 / 2 : ℝ)) ≤ 9).trans (le_max_left _ _))
    have havg' : kernelAverage μ ker t (ball q r) z ≤
        (P * (Real.sqrt t)⁻¹ ^ n * Real.exp ((A + 1) ^ 2 / (4 + 1 / 2))) *
          Real.exp (-(dist x z) ^ 2 / (D * t)) := by
      apply havg.trans
      have he : 2 * (4 + (1 / 2 : ℝ)) * t = 9 * t := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hdecay (by positivity)
    have hpoint' := (hpoint x).trans (mul_le_mul_of_nonneg_left hdecay'
      (mul_nonneg hP.le hpow))
    have hnonneg := (kernelAverage_bounds μ hQ hk ht (ball q r) z).1
    have hnonneg' := hk.nonneg t ht x z
    have habs : |kernelAverage μ ker t (ball q r) z - ker t x z| ≤
        kernelAverage μ ker t (ball q r) z + ker t x z := by
      rw [abs_le]
      constructor <;> linarith
    have hm : |kernelAverage μ ker t (ball q r) z - ker t x z| ≤
        M * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (D * t)) := by
      dsimp only [M]
      nlinarith only [habs, havg', hpoint']
    have hf : 1 ≤ (A + 1) * r * (Real.sqrt t)⁻¹ := by
      have hlt : Real.sqrt t ≤ (A + 1) * r := le_of_not_ge hscale
      simpa only [div_eq_mul_inv] using (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hlt)
    have hmul := mul_le_mul_of_nonneg_left hf
      (by positivity : 0 ≤ M * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (D * t)))
    have he : (M * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (D * t))) *
        ((A + 1) * r * (Real.sqrt t)⁻¹) =
          (M * (A + 1)) * r * (Real.sqrt t)⁻¹ ^ (n + 1) *
            Real.exp (-(dist x z) ^ 2 / (D * t)) := by rw [pow_succ]; ring
    rw [mul_one, he] at hmul
    apply hm.trans (hmul.trans _)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hr.le
    dsimp only [C]
    linarith

end RegularPointCoordinates

end

end OAI
