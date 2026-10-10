import OAI.Geometry.RCD.Transport.AsymmetricMidpointCompression
import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # A midpoint density bound independent of the concentrating endpoint

The inverse support factor is finite for finite positive endpoint bounds.
Its one-sided estimate retains just the initial density. This is the
uniform bound used before passing the other endpoint to a Dirac mass.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem midpointSupportFactor_pos (K : ℝ) {n : ℕ} (hn : 0 < n) (D : ℝ)
    {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) : 0 < midpointSupportFactor K n D C₀ C₁ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < C₀ ^ (-(1 / (n : ℝ))) := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_pos.mpr (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC₀)
  unfold midpointSupportFactor
  apply pos_iff_ne_zero.mpr
  exact pow_ne_zero _ (mul_ne_zero (midpointFloor_pos K n D).ne'
    (lt_of_lt_of_le hp (le_add_right le_rfl)).ne')

theorem midpointSupportFactor_ne_top (K : ℝ) {n : ℕ} (hn : 0 < n) (D : ℝ)
    {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0) :
    midpointSupportFactor K n D C₀ C₁ ≠ ∞ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf (C : ℝ≥0∞) (hC : C ≠ 0) : C ^ (-(1 / (n : ℝ))) ≠ ∞ := by
    rw [ENNReal.rpow_neg]
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hC) (by positivity)).ne'
  exact ENNReal.pow_ne_top
    (ENNReal.mul_ne_top (midpointFloor_ne_top K n D)
      (ENNReal.add_ne_top.mpr ⟨hf C₀ hC₀, hf C₁ hC₁⟩))

theorem midpointSupportFactor_inv_le (K : ℝ) {n : ℕ} (hn : 0 < n) (D : ℝ)
    (C₀ C₁ : ℝ≥0∞) :
    (midpointSupportFactor K n D C₀ C₁)⁻¹ ≤
      C₀ / (midpointFloor K n D) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hle : (midpointFloor K n D) ^ n * C₀⁻¹ ≤
      midpointSupportFactor K n D C₀ C₁ := by
    have hbase : midpointFloor K n D * C₀ ^ (-(1 / (n : ℝ))) ≤
        midpointFloor K n D * (C₀ ^ (-(1 / (n : ℝ))) + C₁ ^ (-(1 / (n : ℝ)))) :=
      mul_le_mul_right (le_add_right le_rfl) _
    have h := pow_le_pow_left' hbase n
    have he : (C₀ ^ (-(1 / (n : ℝ)))) ^ n = C₀⁻¹ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        neg_mul, one_div_mul_cancel hn0, ENNReal.rpow_neg_one]
    rw [mul_pow, he] at h
    exact h
  have hh := ENNReal.inv_le_inv.mpr hle
  have hf0 : (midpointFloor K n D) ^ n ≠ 0 :=
    pow_ne_zero _ (midpointFloor_pos K n D).ne'
  have hft : (midpointFloor K n D) ^ n ≠ ∞ :=
    ENNReal.pow_ne_top (midpointFloor_ne_top K n D)
  rw [ENNReal.mul_inv (Or.inl hf0) (Or.inl hft), inv_inv] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

variable [ProperSpace X]

theorem NoncollapsedRCD.exists_asymmetric_midpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₁ • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤
        (midpointSupportFactor K n (2 * R) C₀ C₁)⁻¹ • hausdorff n X := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : IsFiniteMeasure ((hausdorff n X).restrict (closedBall p (3 * R))) :=
    ⟨by simpa using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  have hz0 := probability_capacity_ne_zero (hausdorff n X) ν₀ h0
  have hz1 := probability_capacity_ne_zero (hausdorff n X) ν₁ h1
  have hn0 : 0 < n := by omega
  exact hX.cd.exists_compressed_midpoint_asymmetric (hausdorff n X) K n ν₀ ν₁
    hC₀ hC₁
    (ENNReal.inv_ne_top.mpr (midpointSupportFactor_pos K hn0 (2 * R) hC₀).ne')
    (ENNReal.inv_ne_zero.mpr (midpointSupportFactor_ne_top K hn0 (2 * R) hz0 hz1))
    h0 h1 (finiteSecondMoment_of_bounded ν₀ p hs0) (finiteSecondMoment_of_bounded ν₁ p hs1)
    p hR hs0 hs1 hn (by rw [inv_inv])

end RegularPointCoordinates

end OAI
