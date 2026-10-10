import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Metric.ShortAverageMass
import OAI.Geometry.RCD.Heat.HeatBlockIntegrals

namespace OAI

/-! # Actual short-time source integrals -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hcompact : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual averaged heat mass, set to zero outside positive times. -/
def cutoffAverageHeatMassAt (M : PositiveBilinearMeasure X E)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) (t : ℝ) : E →L[ℝ] E :=
  if ht : 0 < t then cutoffAverageHeatMass μ hQ hk hχ hcompact M ht s hs hbounded else 0

theorem cutoffAverageHeatMassAt_of_pos (M : PositiveBilinearMeasure X E)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s)
    {t : ℝ} (ht : 0 < t) :
    cutoffAverageHeatMassAt μ hQ hk hχ hcompact M s hs hbounded t =
      cutoffAverageHeatMass μ hQ hk hχ hcompact M ht s hs hbounded := dite_eq_left ht

theorem cutoffAverageHeatMassAt_nonneg (M : PositiveBilinearMeasure X E)
    (hχpos : ∀ z, 0 ≤ χ z) (s : Set X) (hs : MeasurableSet s)
    (hbounded : Bornology.IsBounded s) (t : ℝ) (v : E) :
    0 ≤ ⟪v, cutoffAverageHeatMassAt μ hQ hk hχ hcompact M s hs hbounded t v⟫_ℝ := by
  by_cases ht : 0 < t
  · rw [cutoffAverageHeatMassAt_of_pos μ hQ hk hχ hcompact M s hs hbounded ht,
      cutoffAverageHeatMass_integral]
    exact integral_nonneg fun z => mul_nonneg (hχpos z) (kernelAverage_bounds μ hQ hk ht s z).1
  · simp only [cutoffAverageHeatMassAt, dite_eq_right ht, zero_apply, inner_zero_right, le_refl]

/-- The entire short-time source integral is bounded by the actual
Bochner envelope, with the same uniform constant as the pointwise estimate. -/
theorem exists_short_average_mass_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (m : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
      (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (x : X) (χ : X →ᵇ ℝ),
      ∀ hc : HasCompactSupport (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (i : ℕ) (q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ (m + 2) ≤ μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ t, 0 < t → t ≤ (R / 2 ^ i) ^ 2 →
        ∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean (m + 2),
      |∫ t in (0 : ℝ)..(R / 2 ^ i) ^ 2,
        ⟪v, cutoffAverageHeatMassAt μ hQ hk χ.continuous hc M
          (ball q (R / 2 ^ i)) measurableSet_ball isBounded_ball t v⟫_ℝ| ≤
        C * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
  obtain ⟨C, hC, hb⟩ := exists_short_average_mass_bound μ hQ hk hg m hA hV
  refine ⟨C, hC, ?_⟩
  intro M R hR hR1 x χ hc hχ hzero i q hfinite hvol hcenter hsource v
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  apply short_time_integral_norm_le hs
    (mul_nonneg hC.le ((dyadicBochnerEnvelope_isPositive M (m + 2) x hR.le i).inner_nonneg_right v))
  intro t ht hti
  rw [abs_of_nonneg (cutoffAverageHeatMassAt_nonneg μ hQ hk χ.continuous hc M
    (fun z => (hχ z).1) _ measurableSet_ball isBounded_ball t v),
    cutoffAverageHeatMassAt_of_pos μ hQ hk χ.continuous hc M _ measurableSet_ball isBounded_ball ht]
  exact hb M R hR hR1 x χ hc hχ hzero i q hfinite hvol hcenter t ht hti (hsource t ht hti) v

end RegularPointCoordinates

end

end OAI
