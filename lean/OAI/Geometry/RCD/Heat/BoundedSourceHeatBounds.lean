import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.BoundedDensityGaussian
import OAI.Geometry.RCD.Heat.ShortAverageHeatBound
import OAI.Geometry.RCD.Heat.LongAverageHeatBound

namespace OAI

/-! # Averaged heat estimates for bounded compact source densities -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The short-time average of a bounded source has a scale-independent
bound. All volume assumptions are confined to the working ball. -/
theorem exists_short_bounded_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → R ≤ 1 → ∀ (i : ℕ) (x q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ n ≤ μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ j ≤ i, μ.real (ball x (2 ^ j * (R / 2 ^ i))) ≤ W * (2 ^ j * (R / 2 ^ i)) ^ n) →
      ∀ (t : ℝ), 0 < t → t ≤ (R / 2 ^ i) ^ 2 →
      (∀ z ∈ ball x R, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ (g : X → ℝ) (B : ℝ), 0 ≤ B → (∀ᵐ z ∂μ, |g z| ≤ B) →
      (∀ᵐ z ∂μ, z ∉ ball x R → g z = 0) →
      |∫ z, kernelAverage μ ker t (ball q (R / 2 ^ i)) z * g z ∂μ| ≤ C * B := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_cutoff_short_average_bound μ hQ hk hg n hA hV
  let G := gaussianVolumeMomentConstant n (36 : ℝ)⁻¹
  have hG : 0 ≤ G := gaussianVolumeMomentConstant_nonneg _ _
  refine ⟨C₀ * W * G + 1, by positivity, ?_⟩
  intro R hR hR1 i x q hfinite hvol hcenter hupper t ht htime hsource g B hB hgb hgzero
  let χ := (ball x R).indicator (fun _ : X => (1 : ℝ))
  have hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    by_cases hz : z ∈ ball x R <;> simp [χ, hz]
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hs1 : R / (2 : ℝ) ^ i ≤ 1 :=
    (div_le_self hR.le (one_le_pow₀ (by norm_num))).trans hR1
  have hp := hb χ hχ (R / (2 : ℝ) ^ i) t x q hs hs1 ht htime hfinite hvol hcenter
    (fun z hz => hsource z (by by_contra hn; exact hz (indicator_of_notMem hn _)))
  have hpoint : ∀ z ∈ ball x R,
      |kernelAverage μ ker t (ball q (R / 2 ^ i)) z| ≤
        C₀ / (R / 2 ^ i) ^ n * Real.exp (-(dist x z) ^ 2 / (36 * (R / 2 ^ i) ^ 2)) := by
    intro z hz
    have he := hp z
    rw [show χ z = 1 from indicator_of_mem hz _, one_mul] at he
    rw [abs_of_nonneg (kernelAverage_bounds μ hQ hk ht _ z).1]
    simpa only [div_eq_mul_inv, inv_pow] using he
  have hroot : (2 : ℝ) ^ i * (R / (2 : ℝ) ^ i) = R := by field_simp
  have he := integral_bounded_density_gaussian_le μ n x hs hC₀.le (by norm_num : (0 : ℝ) < 36)
    hW hB i hroot hgb hgzero hpoint hupper
  change _ ≤ C₀ * B * W * G at he
  nlinarith only [he, hB]

end RegularPointCoordinates

end

end OAI
