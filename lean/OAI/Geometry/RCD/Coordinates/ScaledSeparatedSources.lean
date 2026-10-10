import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.SeparatedSourceBounds

namespace OAI

/-! # Separation estimates with constants fixed before the physical radius -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- Rescaling the scalar Gaussian estimate retains its exact inverse-volume power. -/
theorem exists_scaled_separated_gaussian_bound (n : ℕ) {c D : ℝ}
    (hc : 0 < c) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ R s d : ℝ, 0 < R → 0 < s → c * R ≤ d →
      R ^ n * (s⁻¹ ^ n * Real.exp (-d ^ 2 / (D * s ^ 2))) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_separated_gaussian_bound n hc hD
  refine ⟨C, hC, ?_⟩
  intro R s d hR hs hsep
  have h := hb (s / R) (d / R) (div_pos hs hR) ((le_div_iff₀ hR).mpr hsep)
  have he : -(d / R) ^ 2 / (D * (s / R) ^ 2) = -d ^ 2 / (D * s ^ 2) := by
    field_simp [hR.ne']
  rw [he] at h
  have hp : (s / R)⁻¹ ^ n = R ^ n * s⁻¹ ^ n := by
    rw [inv_div, div_pow]
    simp only [div_eq_mul_inv, inv_pow]
  rw [hp] at h
  simpa only [mul_assoc] using h

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The short-time source coefficient scales as inverse volume. -/
theorem exists_scaled_short_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (n : ℕ) {A V c : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r t : ℝ) (x q : X) (S : Set X) (g : X → ℝ),
      0 < R → 0 < r → r ≤ 1 → 0 < t → t ≤ r ^ 2 →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z ∈ S, c * R ≤ dist x z) →
      (∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      Integrable g μ → (∀ᵐ z ∂μ, z ∉ S → g z = 0) →
      |∫ z, kernelAverage μ ker t (ball q r) z * g z ∂μ| ≤
        (C / R ^ n) * ∫ z, |g z| ∂μ := by
  classical
  obtain ⟨C₀, hC₀, hb⟩ := exists_cutoff_short_average_bound μ hQ hk hg n hA hV
  obtain ⟨H, hH, hh⟩ := exists_scaled_separated_gaussian_bound n hc (by norm_num : (0 : ℝ) < 36)
  refine ⟨C₀ * H, mul_pos hC₀ hH, ?_⟩
  intro R r t x q S g hR hr hr1 ht htr hfinite hvol hcenter hsep hsource hgint hgzero
  let χ : X → ℝ := S.indicator (fun _ => 1)
  have hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  apply abs_integral_mul_le_of_bound_on μ hgint (by positivity) hgzero
  intro z hz
  have hb' := hb χ hχ r t x q hr hr1 ht htr hfinite hvol hcenter
    (fun y hy => hsource y (by by_contra hn; simp [χ, hn] at hy)) z
  have hχz : χ z = 1 := by simp [χ, hz]
  rw [hχz, one_mul] at hb'
  rw [abs_of_nonneg (kernelAverage_bounds μ hQ hk ht (ball q r) z).1]
  apply hb'.trans
  apply (le_div_iff₀ (pow_pos hR n)).mpr
  have hm := mul_le_mul_of_nonneg_left (hh R r (dist x z) hR hr (hsep z hz)) hC₀.le
  nlinarith only [hm]

include hk in
/-- The long-time source difference has one extra inverse-radius factor. -/
theorem exists_scaled_long_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V c : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r t : ℝ) (x q : X) (S : Set X) (g : X → ℝ),
      0 < R → 0 < r → 0 < t → t ≤ 1 → r ^ 2 ≤ t →
      μ (ball q r) ≠ ∞ → 0 < μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z ∈ S, c * R ≤ dist x z) →
      (∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      Integrable g μ → (∀ᵐ z ∂μ, z ∉ S → g z = 0) →
      |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) * g z ∂μ| ≤
        (C * r / R ^ (n + 1)) * ∫ z, |g z| ∂μ := by
  obtain ⟨C₀, D, hC₀, hD, hb⟩ := exists_long_average_difference_bound μ hQ hk hg hdiff n hA hV
  obtain ⟨H, hH, hh⟩ := exists_scaled_separated_gaussian_bound (n + 1) hc hD
  refine ⟨C₀ * H, mul_pos hC₀ hH, ?_⟩
  intro R r t x q S g hR hr ht ht1 hrt hfinite hvol hcenter hsep hsource hgint hgzero
  apply abs_integral_mul_le_of_bound_on μ hgint (by positivity) hgzero
  intro z hz
  have h := hb r t x q z hr ht ht1 hrt hfinite hvol hcenter (hsource z hz)
  have hsmall := hh R (Real.sqrt t) (dist x z) hR (Real.sqrt_pos.mpr ht) (hsep z hz)
  rw [Real.sq_sqrt ht.le] at hsmall
  apply h.trans
  apply (le_div_iff₀ (pow_pos hR (n + 1))).mpr
  have hm := mul_le_mul_of_nonneg_left hsmall (mul_pos hC₀ hr).le
  nlinarith only [hm]

end RegularPointCoordinates

end

end OAI
