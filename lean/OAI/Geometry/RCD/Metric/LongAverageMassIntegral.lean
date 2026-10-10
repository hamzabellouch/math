import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Metric.AverageMassTime
import OAI.Geometry.RCD.Metric.LongAverageMass

namespace OAI

/-! # Integrated long-time blocks of the actual full positive source -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual pointwise heat mass as a function of all real times. -/
def cutoffHeatMassAt (M : PositiveBilinearMeasure X E) (t : ℝ) (x : X) : E →L[ℝ] E :=
  if ht : 0 < t then cutoffHeatMass μ hQ hk hχ hc M ht x else 0

omit [IsLocallyFiniteMeasure μ] in
theorem cutoffHeatMassAt_of_pos (M : PositiveBilinearMeasure X E)
    {t : ℝ} (ht : 0 < t) (x : X) :
    cutoffHeatMassAt μ hQ hk hχ hc M t x = cutoffHeatMass μ hQ hk hχ hc M ht x := dite_eq_left ht

/-- Each complete long-time block consumes the displacement factor r/s
in the same full Bochner envelope. -/
theorem exists_long_average_mass_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (m : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
      (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (x : X) (χ : X →ᵇ ℝ),
      ∀ hcompact : HasCompactSupport (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (j : ℕ) (r : ℝ) (q : X),
      0 < r → r ≤ (R / 2 ^ j) / 2 → μ (ball q r) ≠ ∞ →
      0 < μ.real (ball q r) → dist x q ≤ A * r →
      (∀ t ∈ Icc ((R / 2 ^ j) ^ 2 / 4) ((R / 2 ^ j) ^ 2),
        ∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean (m + 2),
      |∫ t in ((R / 2 ^ j) ^ 2 / 4)..(R / 2 ^ j) ^ 2,
        ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.continuous hcompact M
          (ball q r) measurableSet_ball isBounded_ball t -
          cutoffHeatMassAt μ hQ hk χ.continuous hcompact M t x) v⟫_ℝ| ≤
        C * (r / (R / 2 ^ j)) * ⟪v, dyadicBochnerEnvelope M (m + 2) x R j v⟫_ℝ := by
  obtain ⟨C, hC, hb⟩ := exists_long_average_mass_bound μ hQ hk hg hdiff m hA hV
  refine ⟨C, hC, ?_⟩
  intro M R hR hR1 x χ hcompact hχ hzero j r q hr hrs hfinite hvol hcenter hsource v
  have hs : 0 < R / (2 : ℝ) ^ j := div_pos hR (by positivity)
  apply dyadic_time_integral_norm_le hs
    (mul_nonneg (mul_nonneg hC.le (div_pos hr hs).le)
      ((dyadicBochnerEnvelope_isPositive M (m + 2) x hR.le j).inner_nonneg_right v))
  intro t ht
  have htpos : 0 < t := (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1
  rw [cutoffAverageHeatMassAt_of_pos μ hQ hk χ.continuous hcompact M _ measurableSet_ball isBounded_ball htpos,
    cutoffHeatMassAt_of_pos μ hQ hk χ.continuous hcompact M htpos]
  exact hb M R hR hR1 x χ hcompact hχ hzero j r q hr hrs hfinite hvol hcenter t htpos ht (hsource t ht) v

end RegularPointCoordinates

end

end OAI
