import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.HeatMassTimeContinuity
import OAI.Geometry.RCD.Heat.DyadicTimeIntegral

namespace OAI

/-! # Summing every long-time block in the original full-mass envelope -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

private theorem dyadic_radius_ratio {R : ℝ} (hR : 0 < R) {j i : ℕ} (hji : j ≤ i) :
    (R / (2 : ℝ) ^ i) / (R / (2 : ℝ) ^ j) = (1 / 2 : ℝ) ^ (i - j) := by
  have hroot : (2 : ℝ) ^ i * (R / (2 : ℝ) ^ i) = R := by field_simp
  have he := outward_radius_eq_ancestor hroot hji
  rw [← he, one_div_pow]
  rw [mul_comm ((2 : ℝ) ^ (i - j))]
  simpa only [one_div] using div_mul_cancel_left₀ (by positivity : R / (2 : ℝ) ^ i ≠ 0) ((2 : ℝ) ^ (i - j))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- All long-time blocks sum to a fixed multiple of the same envelope
used by the heat decrement, with the original full Bochner measure. -/
theorem exists_long_time_mass_sum_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (m : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
      (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (x : X) (χ : X →ᵇ ℝ),
      ∀ hc : HasCompactSupport (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (i : ℕ) (q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ → 0 < μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ t, 0 < t → t ≤ R ^ 2 →
        ∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean (m + 2),
      |∫ t in (R / 2 ^ i) ^ 2..R ^ 2,
        ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.continuous hc M
          (ball q (R / 2 ^ i)) measurableSet_ball isBounded_ball t -
          cutoffHeatMassAt μ hQ hk χ.continuous hc M t x) v⟫_ℝ| ≤
        C * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
  obtain ⟨C, hC, hb⟩ := exists_long_average_mass_integral_bound μ hQ hk hg hdiff m hA hV
  refine ⟨3 * C, by positivity, ?_⟩
  intro M R hR hR1 x χ hc hχ hzero i q hfinite hvol hcenter hsource v
  let f := fun t => ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.continuous hc M
    (ball q (R / 2 ^ i)) measurableSet_ball isBounded_ball t -
    cutoffHeatMassAt μ hQ hk χ.continuous hc M t x) v⟫_ℝ
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsi : (R / (2 : ℝ) ^ i) ^ 2 ≤ R ^ 2 := by
    apply pow_le_pow_left₀ hs.le
    exact div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hi := cutoffAverageHeatMassAt_difference_intervalIntegrable μ hQ hk χ.continuous hc M
    (ball q (R / (2 : ℝ) ^ i)) measurableSet_ball isBounded_ball x v (sq_pos_of_pos hs) hsi
  have hblock : ∀ j < i, |∫ t in (R / (2 : ℝ) ^ j) ^ 2 / 4..(R / (2 : ℝ) ^ j) ^ 2, f t| ≤
      C * (1 / 2 : ℝ) ^ (i - j) * ⟪v, dyadicBochnerEnvelope M (m + 2) x R j v⟫_ℝ := by
    intro j hji
    have hjradius : R / (2 : ℝ) ^ i ≤ (R / (2 : ℝ) ^ j) / 2 := by
      rw [div_div, ← pow_succ]
      exact div_le_div_of_nonneg_left hR.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hji)
    have hjR : (R / (2 : ℝ) ^ j) ^ 2 ≤ R ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    have he := hb M R hR hR1 x χ hc hχ hzero j (R / (2 : ℝ) ^ i) q hs hjradius
      hfinite hvol hcenter (fun t ht z hz => hsource t
        ((div_pos (sq_pos_of_pos (div_pos hR (by positivity))) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1)
        (ht.2.trans hjR) z hz) v
    simpa only [f, dyadic_radius_ratio hR hji.le] using he
  have htotal := dyadic_time_integral_abs_le f hR i hi _ hblock
  have hnonneg : 0 ≤ C * (1 / 2 : ℝ) ^ (i - i) *
      ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ :=
    mul_nonneg (mul_nonneg hC.le (by positivity))
      ((dyadicBochnerEnvelope_isPositive M (m + 2) x hR.le i).inner_nonneg_right v)
  have hsum := dyadicBochnerEnvelope_time_sum_le M (m + 2) x hR.le i v
  have hle : (∑ j ∈ Finset.range i, C * (1 / 2 : ℝ) ^ (i - j) *
      ⟪v, dyadicBochnerEnvelope M (m + 2) x R j v⟫_ℝ) ≤
      C * (∑ j ∈ Finset.range (i + 1), (1 / 2 : ℝ) ^ (i - j) *
        ⟪v, dyadicBochnerEnvelope M (m + 2) x R j v⟫_ℝ) := by
    rw [Finset.mul_sum, Finset.sum_range_succ]
    simp only [mul_assoc]
    exact le_add_of_nonneg_right (by simpa only [mul_assoc] using hnonneg)
  exact htotal.trans (hle.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsum hC.le]))

end RegularPointCoordinates

end

end OAI
