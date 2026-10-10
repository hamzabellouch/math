import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCollision

namespace OAI

/-!
# Preventing quadratic cancellation at two scales

This is the elementary cancellation step in EKL (2006), Section 4.5.
A normalized quadratic root displacement is bounded away from zero
either at a point of the first annulus or at every sufficiently large
point of the second annulus.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree

theorem normalized_quadratic_two_scales (a b u v ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hnorm : max |a| |b| = 1)
    (hu : ρ ≤ |u|) (huone : |u| ≤ 1) (hv : 4 / ρ ≤ |v|) :
    ρ / 2 ≤ |a * u - b * u ^ 2| ∨ |v| ≤ |a * v - b * v ^ 2| := by
  have ha : |a| ≤ 1 := (le_max_left _ _).trans_eq hnorm
  have hb : |b| ≤ 1 := (le_max_right _ _).trans_eq hnorm
  by_cases hbsmall : |b| < ρ / 2
  · left
    have haone : |a| = 1 := by
      have hb1 : |b| < 1 := by linarith
      have hage : 1 ≤ |a| := (le_max_iff.mp hnorm.ge).resolve_right hb1.not_ge
      exact le_antisymm ha hage
    have hu2 : |u| ^ 2 ≤ 1 := by nlinarith [sq_nonneg (|u| - 1)]
    have hbu : |b| * |u| ^ 2 ≤ ρ / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hu2 (abs_nonneg b)
      nlinarith
    have hrev := abs_add_le (a * u - b * u ^ 2) (b * u ^ 2)
    rw [sub_add_cancel, abs_mul, haone, one_mul, abs_mul, abs_pow] at hrev
    linarith
  · right
    have hbge : ρ / 2 ≤ |b| := le_of_not_gt hbsmall
    have hρv : 4 ≤ ρ * |v| := by
      have h := (div_le_iff₀ hρ).mp hv
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hρv (abs_nonneg v)
    have hquad := mul_le_mul_of_nonneg_right hbge (sq_nonneg |v|)
    have htwo : 2 * |v| ≤ |b| * |v| ^ 2 := by nlinarith
    have hlin : |a| * |v| ≤ |v| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (abs_nonneg v)
    have hrev := abs_add_le (a * v - b * v ^ 2) (-(a * v))
    rw [show (a * v - b * v ^ 2) + -(a * v) = -(b * v ^ 2) by ring,
      abs_neg, abs_mul, abs_pow, abs_neg, abs_mul] at hrev
    linarith

end DukePrimeDegree

end

end OAI
