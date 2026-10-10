import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCoefficientBounds

namespace OAI

/-!
# A positive displacement at one of two annuli

The normalized scale consists of a fixed linear coefficient, the square
root of a quadratic coefficient, and the remaining linear coefficients.
The latter already give a displacement; otherwise the quadratic pivot
cannot cancel at both of the chosen scales.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree

theorem quadratic_two_scales_quarter (a b u v ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (ha : |a| ≤ 1)
    (hnorm : 1 / 4 ≤ max |a| |b|)
    (hu : ρ ≤ |u|) (huone : |u| ≤ 1) (hv : 16 / ρ ≤ |v|) :
    ρ / 8 ≤ |a * u - b * u ^ 2| ∨ |v| ≤ |a * v - b * v ^ 2| := by
  by_cases hbsmall : |b| < ρ / 8
  · left
    have hbquarter : |b| < 1 / 4 := by linarith
    have hage : 1 / 4 ≤ |a| := (le_max_iff.mp hnorm).resolve_right hbquarter.not_ge
    have hu2 : |u| ^ 2 ≤ 1 := by nlinarith [sq_nonneg (|u| - 1)]
    have hbu : |b| * |u| ^ 2 ≤ ρ / 8 := by
      have h := mul_le_mul_of_nonneg_left hu2 (abs_nonneg b)
      nlinarith
    have hAu : ρ / 4 ≤ |a| * |u| := by
      have h1 := mul_le_mul_of_nonneg_right hage (abs_nonneg u)
      nlinarith
    have hrev := abs_add_le (a * u - b * u ^ 2) (b * u ^ 2)
    rw [sub_add_cancel, abs_mul, abs_mul, abs_pow] at hrev
    linarith
  · right
    have hbge : ρ / 8 ≤ |b| := le_of_not_gt hbsmall
    have hρv : 16 ≤ ρ * |v| := by
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

theorem shearing_profile_two_scales (a b L u v ρ : ℝ)
    (hnorm : max |a| (Real.sqrt |b| + L) = 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hu : ρ ≤ |u|) (huone : |u| ≤ 1) (hv : 16 / ρ ≤ |v|) :
    ρ / 8 ≤ max |a * u - b * u ^ 2| (|u| * L) ∨
    ρ / 8 ≤ max |a * v - b * v ^ 2| (|v| * L) := by
  by_cases hLlarge : 1 / 2 ≤ L
  · left
    have hmul := mul_le_mul_of_nonneg_left hLlarge (abs_nonneg u)
    have hlow : ρ / 8 ≤ |u| * L := by linarith
    exact hlow.trans (le_max_right _ _)
  · have ha : |a| ≤ 1 := (le_max_left _ _).trans_eq hnorm
    have hquarter : 1 / 4 ≤ max |a| |b| := by
      by_cases haquarter : 1 / 4 ≤ |a|
      · exact haquarter.trans (le_max_left _ _)
      · have ha1 : |a| < 1 := by linarith
        have hu1 : 1 ≤ Real.sqrt |b| + L :=
          (le_max_iff.mp hnorm.ge).resolve_left ha1.not_ge
        have hbquarter : 1 / 4 ≤ |b| := by
          nlinarith [Real.sq_sqrt (abs_nonneg b), Real.sqrt_nonneg |b|]
        exact hbquarter.trans (le_max_right _ _)
    rcases quadratic_two_scales_quarter a b u v ρ hρ hρone ha hquarter hu huone hv with h | h
    · exact Or.inl (h.trans (le_max_left _ _))
    · have hvρ : ρ / 8 ≤ |v| := by
        have h := (div_le_iff₀ hρ).mp hv
        nlinarith [sq_nonneg ρ]
      exact Or.inr (hvρ.trans (h.trans (le_max_left _ _)))

end DukePrimeDegree

end

end OAI
