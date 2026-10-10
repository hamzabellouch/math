import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.BoundedSourceHeatBounds

namespace OAI

/-! # Long-time displacement bound for the bounded curvature source -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- On each long-time block the bounded source gains the displacement
ratio r/s. The volume bound is only needed on the working ball. -/
theorem exists_long_bounded_source_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → R ≤ 1 → ∀ (i : ℕ) (r : ℝ) (x q : X),
      0 < r → r ≤ (R / 2 ^ i) / 2 → μ (ball q r) ≠ ∞ → 0 < μ.real (ball q r) →
      dist x q ≤ A * r →
      (∀ j ≤ i, μ.real (ball x (2 ^ j * (R / 2 ^ i))) ≤ W * (2 ^ j * (R / 2 ^ i)) ^ n) →
      ∀ (t : ℝ), 0 < t → t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2) →
      (∀ z ∈ ball x R, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ (g : X → ℝ) (B : ℝ), 0 ≤ B → (∀ᵐ z ∂μ, |g z| ≤ B) →
      (∀ᵐ z ∂μ, z ∉ ball x R → g z = 0) →
      |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) * g z ∂μ| ≤
        C * B * (r / (R / 2 ^ i)) := by
  obtain ⟨C₀, D, hC₀, hD, hb⟩ := exists_long_average_difference_bound μ hQ hk hg hdiff n hA hV
  let H := C₀ * (2 : ℝ) ^ (n + 1)
  let G := gaussianVolumeMomentConstant n D⁻¹
  have hH : 0 < H := by dsimp [H]; positivity
  have hG : 0 ≤ G := gaussianVolumeMomentConstant_nonneg _ _
  refine ⟨H * W * G + 1, by positivity, ?_⟩
  intro R hR hR1 i r x q hr hrs hfinite hvol hcenter hupper t ht htime hsource g B hB hgb hgzero
  let s := R / (2 : ℝ) ^ i
  have hs : 0 < s := div_pos hR (by positivity)
  have hsR : s ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hsqrt : s / 2 ≤ Real.sqrt t := by
    have hsq := Real.sq_sqrt ht.le
    have hn := Real.sqrt_nonneg t
    change s ^ 2 / 4 ≤ t ∧ t ≤ s ^ 2 at htime
    nlinarith
  have hsqrtpos := Real.sqrt_pos.mpr ht
  have ht1 : t ≤ 1 := htime.2.trans (by nlinarith)
  have hrtime : r ^ 2 ≤ t := by
    have hh := (sq_le_sq₀ hr.le (half_pos hs).le).mpr hrs
    nlinarith [htime.1]
  have hinv : (Real.sqrt t)⁻¹ ≤ 2 * s⁻¹ := by
    have h := one_div_le_one_div_of_le (half_pos hs) hsqrt
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul] using h
  have hpow := pow_le_pow_left₀ (inv_pos.mpr hsqrtpos).le hinv (n + 1)
  let α := H * (r / s)
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hcoef : C₀ * r * (Real.sqrt t)⁻¹ ^ (n + 1) ≤ α / s ^ n := by
    apply (mul_le_mul_of_nonneg_left hpow (mul_pos hC₀ hr).le).trans_eq
    dsimp only [α, H]
    rw [mul_pow, pow_succ (s⁻¹)]
    simp only [inv_pow]
    field_simp [hs.ne']
  have hpoint : ∀ z ∈ ball x R,
      |kernelAverage μ ker t (ball q r) z - ker t x z| ≤
        α / s ^ n * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) := by
    intro z hz
    have hraw := hb r t x q z hr ht ht1 hrtime hfinite hvol hcenter (hsource z hz)
    have he : Real.exp (-(dist x z) ^ 2 / (D * t)) ≤
        Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have h := div_le_div_of_nonneg_left (sq_nonneg (dist x z)) (mul_pos hD ht)
        (mul_le_mul_of_nonneg_left htime.2 hD.le)
      simpa only [neg_div] using neg_le_neg h
    exact hraw.trans (mul_le_mul hcoef he (Real.exp_pos _).le (div_nonneg hα (pow_pos hs n).le))
  have hroot : (2 : ℝ) ^ i * s = R := by dsimp only [s]; field_simp
  have he := integral_bounded_density_gaussian_le μ n x hs hα hD hW hB i hroot hgb hgzero hpoint hupper
  change _ ≤ α * B * W * G at he
  have hrnonneg : 0 ≤ r / s := (div_pos hr hs).le
  change _ ≤ (H * W * G + 1) * B * (r / s)
  dsimp only [α] at he
  nlinarith only [he, mul_nonneg hB hrnonneg]

end RegularPointCoordinates

end

end OAI
