import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.SeparatedGaussianBound
import OAI.Geometry.RCD.Heat.ShortAverageHeatBound
import OAI.Geometry.RCD.Heat.LongAverageHeatBound
import OAI.Geometry.RCD.Sobolev.CutoffErrorEstimates

namespace OAI

/-! # Actual L1 source bounds away from the heat pole -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- Positive separation controls the whole short-time average of an actual
integrable source. No L2 regularity of the source is required. -/
theorem exists_separated_short_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (n : ℕ) {A V δ : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℝ) (x q : X) (S : Set X) (g : X → ℝ),
      0 < r → r ≤ 1 → 0 < t → t ≤ r ^ 2 →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z ∈ S, δ ≤ dist x z) →
      (∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      Integrable g μ → (∀ᵐ z ∂μ, z ∉ S → g z = 0) →
      |∫ z, kernelAverage μ ker t (ball q r) z * g z ∂μ| ≤ C * ∫ z, |g z| ∂μ := by
  classical
  obtain ⟨C₀, hC₀, hb⟩ := exists_cutoff_short_average_bound μ hQ hk hg n hA hV
  obtain ⟨H, hH, hh⟩ := exists_separated_gaussian_bound n hδ (by norm_num : (0 : ℝ) < 36)
  refine ⟨C₀ * H, mul_pos hC₀ hH, ?_⟩
  intro r t x q S g hr hr1 ht htr hfinite hvol hcenter hsep hsource hgint hgzero
  let χ : X → ℝ := S.indicator (fun _ => 1)
  have hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  apply abs_integral_mul_le_of_bound_on μ hgint (mul_pos hC₀ hH).le hgzero
  intro z hz
  have hb' := hb χ hχ r t x q hr hr1 ht htr hfinite hvol hcenter
    (fun y hy => hsource y (by by_contra hn; simp [χ, hn] at hy)) z
  have hχz : χ z = 1 := by simp [χ, hz]
  rw [hχz, one_mul] at hb'
  rw [abs_of_nonneg (kernelAverage_bounds μ hQ hk ht (ball q r) z).1]
  exact hb'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hh r (dist x z) hr (hsep z hz)) hC₀.le)

include hk in
/-- Above the averaging scale, separation leaves an extra factor of the
averaging radius in the actual difference pairing. -/
theorem exists_separated_long_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V δ : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℝ) (x q : X) (S : Set X) (g : X → ℝ),
      0 < r → 0 < t → t ≤ 1 → r ^ 2 ≤ t →
      μ (ball q r) ≠ ∞ → 0 < μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z ∈ S, δ ≤ dist x z) →
      (∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      Integrable g μ → (∀ᵐ z ∂μ, z ∉ S → g z = 0) →
      |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) * g z ∂μ| ≤
        C * r * ∫ z, |g z| ∂μ := by
  obtain ⟨C₀, D, hC₀, hD, hb⟩ := exists_long_average_difference_bound μ hQ hk hg hdiff n hA hV
  obtain ⟨H, hH, hh⟩ := exists_separated_gaussian_bound (n + 1) hδ hD
  refine ⟨C₀ * H, mul_pos hC₀ hH, ?_⟩
  intro r t x q S g hr ht ht1 hrt hfinite hvol hcenter hsep hsource hgint hgzero
  apply abs_integral_mul_le_of_bound_on μ hgint (by positivity) hgzero
  intro z hz
  have h := hb r t x q z hr ht ht1 hrt hfinite hvol hcenter (hsource z hz)
  have hsmall := hh (Real.sqrt t) (dist x z) (Real.sqrt_pos.mpr ht) (hsep z hz)
  rw [Real.sq_sqrt ht.le] at hsmall
  exact h.trans (by
    have hm := mul_le_mul_of_nonneg_left hsmall (mul_pos hC₀ hr).le
    convert hm using 1 <;> ring)

end RegularPointCoordinates

end

end OAI
