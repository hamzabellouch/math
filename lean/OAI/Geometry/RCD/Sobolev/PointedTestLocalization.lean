import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Pulling a compact interior test back to a physical interior ball -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_test_support_inside {n : ℕ} {p : X} {r S ε ρ τ : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hgap : ρ+2*ε ≤ τ)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    (φ : Euclidean n → ℝ) (hs : Function.support φ ⊆ ball 0 ρ)
    {x : X} (hx : x ∈ ball p (S*r)) (hφ : φ (V x) ≠ 0) : x ∈ ball p (τ*r) := by
  have hn : ‖V x‖ < ρ := by simpa only [mem_ball,dist_zero_right] using hs hφ
  have hd := (abs_le.mp (pointed_radial_distance hr hS hV hx.le)).1
  apply (div_lt_iff₀ hr).mp
  linarith

theorem pointed_test_integral_localization [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) {p : X} {r S ε ρ τ : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hgap : ρ+2*ε ≤ τ) (hτS : τ ≤ S)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    (φ : Euclidean n → ℝ) (hs : Function.support φ ⊆ ball 0 ρ) (f : X → ℝ)
    (hball : MeasurableSet (ball p (S*r))) :
    (∫ x in ball p (τ*r), φ (V x)*f x ∂μ) =
      ∫ x in ball p (S*r), φ (V x)*f x ∂μ := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hball
    (ball_subset_ball (mul_le_mul_of_nonneg_right hτS hr.le))
  intro x hx
  have hz : φ (V x) = 0 := by
    by_contra hn
    exact hx.2 (pointed_test_support_inside hr hS hgap hV φ hs hx.1 hn)
  rw [hz,zero_mul]

end RegularPointCoordinates

end

end OAI
