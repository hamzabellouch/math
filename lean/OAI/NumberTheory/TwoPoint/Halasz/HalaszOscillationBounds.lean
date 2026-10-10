import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleOscillation

namespace OAI

/-! Pointwise bounds for the exact twice-integrated affine amplitude. -/
namespace TwoPointCorrelations

lemma halasz_log_amplitude2_bound (u v m c x a lam W : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hlam : 0 < lam)
    (hs : lam ≤ |halaszLogSlope u v x|) (hw : |m*x+c| ≤ W) :
    |halaszLogAmplitude2 u v m c x| ≤
      |m|/lam^2 + W*|u|/(a^2*lam^3) := by
  have hx : 0 ≤ x := (ha.trans_le hax).le
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  unfold halaszLogAmplitude2
  calc
    _ ≤ |m/(halaszLogSlope u v x)^2| +
        |(m*x+c)*u/(x^2*(halaszLogSlope u v x)^3)| := abs_add_le _ _
    _ = |m|/|halaszLogSlope u v x|^2 +
        |m*x+c| *|u|/(x^2*|halaszLogSlope u v x|^3) := by
      simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hx]
    _ ≤ _ := by
      gcongr

lemma halasz_log_amplitude2_deriv_bound (u v m c x a lam W : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hlam : 0 < lam)
    (hs : lam ≤ |halaszLogSlope u v x|) (hw : |m*x+c| ≤ W) :
    |halaszLogAmplitude2Deriv u v m c x| ≤
      3*|m| *|u|/(a^2*lam^3) + 2*W*|u|/(a^3*lam^3) +
        3*W*u^2/(a^4*lam^4) := by
  have hx : 0 ≤ x := (ha.trans_le hax).le
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  unfold halaszLogAmplitude2Deriv
  calc
    _ ≤ |3*m*u/(x^2*(halaszLogSlope u v x)^3)| +
        |2*(m*x+c)*u/(x^3*(halaszLogSlope u v x)^3)| +
        |3*(m*x+c)*u^2/(x^4*(halaszLogSlope u v x)^4)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 3*|m| *|u|/(x^2*|halaszLogSlope u v x|^3) +
        2*|m*x+c| *|u|/(x^3*|halaszLogSlope u v x|^3) +
        3*|m*x+c| *u^2/(x^4*|halaszLogSlope u v x|^4) := by
      simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hx,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), sq_abs]
    _ ≤ _ := by
      gcongr

open MeasureTheory

lemma halasz_log_remainder_integral (u v m c A a b lam W : ℝ)
    (hA : 0 < A) (hAa : A ≤ a) (hab : a ≤ b) (hlam : 0 < lam)
    (hs : ∀ x ∈ Set.Icc a b, lam ≤ |halaszLogSlope u v x|)
    (hw : ∀ x ∈ Set.Icc a b, |m*x+c| ≤ W) :
    ‖∫ x in a..b, (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x‖ ≤
      (3*|m| *|u|/(A^2*lam^3) + 2*W*|u|/(A^3*lam^3) +
        3*W*u^2/(A^4*lam^4))*(b-a) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (C := 3*|m| *|u|/(A^2*lam^3) + 2*W*|u|/(A^3*lam^3) + 3*W*u^2/(A^4*lam^4))
    (f := fun x => (halaszLogAmplitude2Deriv u v m c x:ℂ)*halaszLogPhase u v x) (by
      intro x hx
      have hx' : x ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩
      rw [norm_mul, halasz_log_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact halasz_log_amplitude2_deriv_bound u v m c x A lam W hA
        (hAa.trans hx'.1) hlam (hs x hx') (hw x hx'))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh

end TwoPointCorrelations

end OAI
