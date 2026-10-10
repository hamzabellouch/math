import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Squared-distance value control from the actual metric approximation -/

open Metric
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- A centered metric approximation controls the actual coordinate norm. -/
theorem IsPointedApproximation.centered_norm_error {n : ℕ} {p : X} {r R ε : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) {f : X → Euclidean n}
    (hf : IsPointedApproximation p 0 r R ε f) (hfp : f p = 0)
    {x : X} (hx : dist x p ≤ R * r) :
    |‖f x‖ - dist x p / r| ≤ ε ∧ ‖f x‖ ≤ R + ε := by
  have hpp : dist p p ≤ R * r := by simpa only [dist_self] using mul_nonneg hR hr.le
  have hdist := hf.2.1 x p hx hpp
  rw [hfp, dist_zero_right] at hdist
  exact ⟨hdist, by linarith [(abs_le.mp hdist).2, (div_le_iff₀ hr).mpr hx]⟩

/-- Squaring the norm incurs only the explicit factor coming from the
bounded testing ball. This is the value estimate in radial convergence. -/
theorem IsPointedApproximation.quadratic_value_error {n : ℕ} {p : X} {r R ε : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) {f : X → Euclidean n}
    (hf : IsPointedApproximation p 0 r R ε f) (hfp : f p = 0)
    {x : X} (hx : dist x p ≤ R * r) :
    |dist p x ^ 2 / 2 - r ^ 2 * ‖f x‖ ^ 2 / 2| ≤
      r ^ 2 * (ε * (2 * R + ε) / 2) := by
  obtain ⟨hd, hn⟩ := hf.centered_norm_error hr hR hfp hx
  have hd₀ : 0 ≤ dist x p / r := div_nonneg dist_nonneg hr.le
  have hdR : dist x p / r ≤ R := (div_le_iff₀ hr).mpr hx
  have hab : |dist x p / r + ‖f x‖| ≤ 2 * R + ε := by
    rw [abs_of_nonneg (add_nonneg hd₀ (norm_nonneg _))]
    linarith
  have hsq : |(dist x p / r) ^ 2 - ‖f x‖ ^ 2| ≤ ε * (2 * R + ε) := by
    rw [sq_sub_sq, abs_mul, abs_sub_comm]
    exact (mul_le_mul hab hd (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
  have heq : dist p x ^ 2 / 2 - r ^ 2 * ‖f x‖ ^ 2 / 2 =
      (r ^ 2 / 2) * ((dist x p / r) ^ 2 - ‖f x‖ ^ 2) := by
    rw [dist_comm p x]
    field_simp
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / 2)]
  have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ r ^ 2 / 2)
  nlinarith

end RegularPointCoordinates

end

end OAI
