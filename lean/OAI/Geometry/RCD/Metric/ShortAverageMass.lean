import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.ShortAverageHeatBound
import OAI.Geometry.RCD.Metric.AverageMassEnvelope
import OAI.Geometry.RCD.Heat.GaussianUpperHeatIncrement
import OAI.Geometry.RCD.Metric.DyadicMassReindex
import OAI.Geometry.RCD.Sobolev.DyadicBochnerMass

namespace OAI

/-! # The short-time average of the full source has the actual dyadic envelope -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- The short-time local positive source is bounded uniformly on the
whole interval, before time integration and polarization. -/
theorem exists_short_average_mass_bound (hg : HasCoordinateHeatBounds μ ker)
    (m : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
      (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (x : X) (χ : X →ᵇ ℝ),
      ∀ hcompact : HasCompactSupport (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (i : ℕ) (q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ (m + 2) ≤ μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) → ∀ (t : ℝ) (ht : 0 < t), t ≤ (R / 2 ^ i) ^ 2 →
      (∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean (m + 2),
      (R / 2 ^ i) ^ 2 * ⟪v, cutoffAverageHeatMass μ hQ hk χ.continuous hcompact
        M ht (ball q (R / 2 ^ i)) measurableSet_ball isBounded_ball v⟫_ℝ ≤
        C * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_cutoff_short_average_bound μ hQ hk hg (m + 2) hA hV
  let G := gaussianMassConvolutionConstant m ((36 : ℝ)⁻¹)
  have hG : 0 ≤ G := gaussianMassConvolutionConstant_nonneg _ _
  refine ⟨C₀ * (G + 1), by positivity, ?_⟩
  intro M R hR hR1 x χ hcompact hχ hzero i q hfinite hvol hcenter t ht hti hsource v
  let s := R / (2 : ℝ) ^ i
  have hs : 0 < s := div_pos hR (by positivity)
  have hs1 : s ≤ 1 := (div_le_self hR.le (one_le_pow₀ (by norm_num))).trans hR1
  have hpoint := hbound χ hχ s t x q hs hs1 ht hti hfinite hvol hcenter hsource
  have hroot : (2 : ℝ) ^ i * s = R := by dsimp only [s]; field_simp
  have hdisplace : ∀ a : ℝ, 0 ≤ a → ∀ z, a * s ≤ dist x z →
      χ z * kernelAverage μ ker t (ball q s) z ≤ (C₀ / s ^ (m + 2)) * Real.exp (-a ^ 2 / 36) := by
    intro a ha z hz
    have hd : (a * s) ^ 2 ≤ (dist x z) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg ha hs.le) dist_nonneg).mpr hz
    have hh := div_le_div_of_nonneg_right hd (by positivity : 0 ≤ 36 * s ^ 2)
    have he : (a * s) ^ 2 / (36 * s ^ 2) = a ^ 2 / 36 := by field_simp
    rw [he] at hh
    have hp := (hpoint z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hh))
      (mul_nonneg hC₀.le (pow_nonneg (inv_pos.mpr hs).le _)))
    simpa only [div_eq_mul_inv, inv_pow, neg_mul] using hp
  have hb := scaled_cutoffAverageHeatMass_le_geometric μ hQ hk χ.continuous hcompact
    M m x hs ht (ball q s) measurableSet_ball isBounded_ball hC₀.le
    (by norm_num : (0 : ℝ) < 36⁻¹) le_rfl i
    (fun j _ z hz => shell_bound_of_displacement x hs _ hdisplace j hz)
    (fun z hz => by rw [hroot] at hz; simp only [hzero z hz, zero_mul]; exact le_rfl) v
  let S := ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) *
    ⟪v, dyadicBochnerMass M (m + 2) x R j v⟫_ℝ
  have he : (∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ j *
      (((2 ^ j * s) ^ 2 / (2 ^ j * s) ^ (m + 2)) *
        (M.measure v).real (ball x (2 ^ j * s)))) = S := by
    rw [outward_sum_eq_inward_sum (fun r => (r ^ 2 / r ^ (m + 2)) *
      (M.measure v).real (ball x r)) (3 / 4) i hroot]
    simp only [S, dyadicBochnerMass_inner]
  rw [he] at hb
  simp only [mul_zero, zero_mul, add_zero] at hb
  rw [dyadicBochnerEnvelope_inner]
  change _ ≤ C₀ * (G + 1) * ((3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 + S)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) ((dyadicBochnerMass_isPositive M (m + 2) x hR.le j).inner_nonneg_right v)
  have hp : 0 ≤ (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 := by positivity
  change _ ≤ C₀ * G * S at hb
  nlinarith only [hb, hS, mul_nonneg (mul_nonneg hC₀.le (by linarith : 0 ≤ G + 1)) hp,
    mul_nonneg hC₀.le hS]

end RegularPointCoordinates

end

end OAI
