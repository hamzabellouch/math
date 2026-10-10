import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.LongBoundedSource
import OAI.Geometry.RCD.Harmonic.AveragedLpPairing
import OAI.Geometry.RCD.Heat.DyadicTimeIntegral

namespace OAI

/-! # Integrating the bounded curvature and endpoint source estimates -/

open Set Metric MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The complete short-time bounded-source contribution has the square
of the averaging radius. -/
theorem exists_short_bounded_source_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → R ≤ 1 → ∀ (i : ℕ) (x q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ n ≤ μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ j ≤ i, μ.real (ball x (2 ^ j * (R / 2 ^ i))) ≤ W * (2 ^ j * (R / 2 ^ i)) ^ n) →
      (∀ t, 0 < t → t ≤ R ^ 2 → ∀ z ∈ ball x R,
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ (f : Lp ℝ 2 μ) (B : ℝ), 0 ≤ B → (∀ᵐ z ∂μ, |f z| ≤ B) →
      (∀ᵐ z ∂μ, z ∉ ball x R → f z = 0) →
      |∫ t in (0 : ℝ)..(R / 2 ^ i) ^ 2,
        ∫ z, kernelAverage μ ker t (ball q (R / 2 ^ i)) z * f z ∂μ| ≤
        C * B * (R / 2 ^ i) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_short_bounded_source_bound μ hQ hk hg n hA hV hW
  refine ⟨C, hC, ?_⟩
  intro R hR hR1 i x q hfinite hvol hcenter hupper hsource f B hB hfb hfzero
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsR : (R / (2 : ℝ) ^ i) ^ 2 ≤ R ^ 2 := by
    apply pow_le_pow_left₀ hs.le
    exact div_le_self hR.le (one_le_pow₀ (by norm_num))
  apply short_time_integral_norm_le hs (by positivity)
  intro t ht htime
  have he := hb R hR hR1 i x q hfinite hvol hcenter hupper t ht htime
    (hsource t ht (htime.trans hsR)) f B hB hfb hfzero
  nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (R / (2 : ℝ) ^ i))]

include hk in
/-- All long-time bounded-source blocks sum to r times the working
radius. This is the gain needed for the curvature contribution. -/
theorem exists_long_bounded_source_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (n : ℕ) {A V W : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → R ≤ 1 → ∀ (i : ℕ) (x q : X),
      μ (ball q (R / 2 ^ i)) ≠ ∞ → 0 < μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ j, μ.real (ball x (R / 2 ^ j)) ≤ W * (R / 2 ^ j) ^ n) →
      (∀ t, 0 < t → t ≤ R ^ 2 → ∀ z ∈ ball x R,
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ (f : Lp ℝ 2 μ) (B : ℝ), 0 ≤ B → (∀ᵐ z ∂μ, |f z| ≤ B) →
      (∀ᵐ z ∂μ, z ∉ ball x R → f z = 0) →
      |∫ t in (R / 2 ^ i) ^ 2..R ^ 2,
        ∫ z, (kernelAverage μ ker t (ball q (R / 2 ^ i)) z - ker t x z) * f z ∂μ| ≤
        C * B * (R / 2 ^ i) * R := by
  obtain ⟨C, hC, hb⟩ := exists_long_bounded_source_bound μ hQ hk hg hdiff n hA hV hW
  refine ⟨2 * C, by positivity, ?_⟩
  intro R hR hR1 i x q hfinite hvol hcenter hupper hsource f B hB hfb hfzero
  let F := fun t => ∫ z, (kernelAverage μ ker t (ball q (R / 2 ^ i)) z - ker t x z) * f z ∂μ
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsR : (R / (2 : ℝ) ^ i) ^ 2 ≤ R ^ 2 := by
    apply pow_le_pow_left₀ hs.le
    exact div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hi := kernelAverage_difference_lp_intervalIntegrable μ hQ hk
    (ball q (R / (2 : ℝ) ^ i)) measurableSet_ball hfinite x f (sq_pos_of_pos hs) hsR
  have hblock : ∀ j < i,
      |∫ t in (R / (2 : ℝ) ^ j) ^ 2 / 4..(R / (2 : ℝ) ^ j) ^ 2, F t| ≤
        C * B * (R / (2 : ℝ) ^ i) * (R / (2 : ℝ) ^ j) := by
    intro j hji
    have hj : 0 < R / (2 : ℝ) ^ j := div_pos hR (by positivity)
    have hrj : R / (2 : ℝ) ^ i ≤ (R / (2 : ℝ) ^ j) / 2 := by
      rw [div_div, ← pow_succ]
      exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hji)
    have hjR : (R / (2 : ℝ) ^ j) ^ 2 ≤ R ^ 2 := by
      apply pow_le_pow_left₀ hj.le
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    apply dyadic_time_integral_norm_le hj (by positivity)
    intro t htime
    have ht : 0 < t := (div_pos (sq_pos_of_pos hj) (by norm_num : (0 : ℝ) < 4)).trans_le htime.1
    have hroot : (2 : ℝ) ^ j * (R / (2 : ℝ) ^ j) = R := by field_simp
    have he := hb R hR hR1 j (R / (2 : ℝ) ^ i) x q hs hrj hfinite hvol hcenter
      (fun k hk => by
        have he := outward_radius_eq_ancestor hroot (Nat.sub_le j k)
        simp only [Nat.sub_sub_self hk] at he
        rw [he]
        exact hupper (j - k))
      t ht htime (hsource t ht (htime.2.trans hjR)) f B hB hfb hfzero
    have hm := mul_le_mul_of_nonneg_left he (sq_nonneg (R / (2 : ℝ) ^ j))
    apply hm.trans_eq
    field_simp
  have he := dyadic_time_integral_abs_le F hR i hi _ hblock
  have hsum : (∑ j ∈ Finset.range i, C * B * (R / (2 : ℝ) ^ i) * (R / (2 : ℝ) ^ j)) =
      C * B * (R / (2 : ℝ) ^ i) * R * ∑ j ∈ Finset.range i, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_eq_mul_inv, one_div_pow]
    ring
  rw [hsum] at he
  have hbound := mul_le_mul_of_nonneg_left (sum_geometric_two_le i)
    (by positivity : 0 ≤ C * B * (R / (2 : ℝ) ^ i) * R)
  nlinarith only [he, hbound]

end RegularPointCoordinates

end

end OAI
