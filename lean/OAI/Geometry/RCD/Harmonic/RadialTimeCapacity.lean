import OAI.Geometry.RCD.Transport.RadialTimeCompression
import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # Source-density control for arbitrary-time radial contraction -/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

theorem timeSupportFactor_eq {n : ℕ} (hn : 0 < n) (β C₀ : ℝ≥0∞) :
    timeSupportFactor n β C₀ = β ^ n * C₀⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold timeSupportFactor
  rw [mul_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, neg_mul,
    one_div_mul_cancel hn0, ENNReal.rpow_neg_one]

theorem timeSupportFactor_inv {n : ℕ} (hn : 0 < n) {β : ℝ≥0∞}
    (hβ0 : β ≠ 0) (hβtop : β ≠ ∞) (C₀ : ℝ≥0∞) :
    (timeSupportFactor n β C₀)⁻¹ = C₀ / β ^ n := by
  rw [timeSupportFactor_eq hn,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hβ0)) (Or.inl (ENNReal.pow_ne_top hβtop)),
    inv_inv, div_eq_mul_inv, mul_comm]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_time_compression {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₁ • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (t : Time) {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβtop : β ≠ ∞)
    (s₀ s₁ : Set X) (hs₀ : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs₁ : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y)) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ t) ≤ (C₀ / β ^ n) • hausdorff n X := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : IsFiniteMeasure ((hausdorff n X).restrict (closedBall p (3 * R))) :=
    ⟨by simpa using hX.finiteOnBounded (closedBall p (3 * R)) isBounded_closedBall⟩
  have hz0 := probability_capacity_ne_zero (hausdorff n X) ν₀ h0
  have hC : C₀ / β ^ n ≠ ∞ := ENNReal.div_ne_top hC₀ (pow_ne_zero _ hβ0)
  have hCpos : C₀ / β ^ n ≠ 0 := (ENNReal.div_pos hz0 (ENNReal.pow_ne_top hβtop)).ne'
  apply hX.cd.exists_compressed_time (hausdorff n X) K n ν₀ ν₁ hC₀ hC₁ hC hCpos
    h0 h1 (finiteSecondMoment_of_bounded ν₀ p hs0) (finiteSecondMoment_of_bounded ν₁ p hs1)
    p hR hs0 hs1 hn t β s₀ s₁ hs₀ hs₁ hβ
  rw [← timeSupportFactor_inv (by omega : 0 < n) hβ0 hβtop C₀, inv_inv]

end RegularPointCoordinates

end OAI
