import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorVertical
import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleVerticalLimit

namespace OAI

/-! # Vanishing horizontal edges for the actual zero detector -/

namespace Ostmann

open Complex MeasureTheory Filter Set
open scoped Topology Interval

 theorem densityDetector_high_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (x u : ℝ) (hx : 1 / 2 - s.re ≤ x) (hx2 : x ≤ 2) (hu : 1 ≤ |u|) :
    ‖densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)‖ ≤
      2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) / |u| ^ 2 := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hup : 0 < |u| := by linarith
  have hn := densityDetector_numerator_bound χ X s hs hs1 Y hY x u hx hx2
  have hk := densityDetectorKernel_high_bound x u hup
  rw [densityDetectorIntegrand, norm_mul]
  calc
    _ ≤ (K * (1 + |u|)) * (|u| ^ 3)⁻¹ := mul_le_mul hn hk (norm_nonneg _) (by positivity)
    _ ≤ (K * (2 * |u|)) * (|u| ^ 3)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hK
      linarith
    _ = 2 * K / |u| ^ 2 := by field_simp

 theorem densityDetector_horizontal_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (u : ℝ) (hu : 1 ≤ |u|) :
    ‖∫ x in (1 / 2 - s.re)..2, densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)‖ ≤
      (2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) *
        |2 - (1 / 2 - s.re)|) / |u| ^ 2 := by
  have hab : 1 / 2 - s.re ≤ 2 := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x (hx : x ∈ Ι (1 / 2 - s.re) 2) => densityDetector_high_bound χ X s hs hs1 Y hY x u
      (by rw [uIoc_of_le hab] at hx; exact hx.1.le)
      (by rw [uIoc_of_le hab] at hx; exact hx.2) hu)
  convert h using 1
  ring

 theorem densityDetector_horizontal_tendsto (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) :
    Tendsto (fun u : ℝ => ∫ x in (1 / 2 - s.re)..2,
      densityDetectorIntegrand χ X s Y ((x : ℂ) + u * I)) atTop (𝓝 0) ∧
    Tendsto (fun u : ℝ => ∫ x in (1 / 2 - s.re)..2,
      densityDetectorIntegrand χ X s Y ((x : ℂ) + (-u) * I)) atTop (𝓝 0) := by
  let K := 2 * (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) * |2 - (1 / 2 - s.re)|
  have ht : Tendsto (fun u : ℝ => K / u ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))).const_mul K
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    simpa only [abs_of_nonneg (by linarith : 0 ≤ u)] using
      densityDetector_horizontal_bound χ X s hs hs1 Y hY u (by rwa [abs_of_nonneg (by linarith)])
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hb := densityDetector_horizontal_bound χ X s hs hs1 Y hY (-u)
      (by simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ u)] using hu)
    simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ u), Complex.ofReal_neg] using hb

end Ostmann

end OAI
