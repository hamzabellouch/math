import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularSmallBall

namespace OAI

/-! Explicit bounds on the lower-order terms of the regular two-channel system. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegular_coupling_bound (A B C D F G FP GP : ℂ) (t K : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) (hC : ‖C‖ ≤ K) (hD : ‖D‖ ≤ K) :
    -((star F * (-Complex.I * (t / 2 : ℝ) * FP + A * F + B * G)).re +
      (star G * (Complex.I * (t / 2 : ℝ) * GP + C * G + D * F)).re) ≤
        (2 * K + 1) * (‖F‖ ^ 2 + ‖G‖ ^ 2) + (‖FP‖ ^ 2 + ‖GP‖ ^ 2) / 2 := by
  have hnorm (I : ℂ) (hI : ‖I‖ = 1) (X XP U V Y : ℂ)
      (hU : ‖U‖ ≤ K) (hV : ‖V‖ ≤ K) :
      ‖I * (t / 2 : ℝ) * XP + U * X + V * Y‖ ≤
        ‖XP‖ / 2 + K * ‖X‖ + K * ‖Y‖ := by
    calc
      _ ≤ ‖I * (t / 2 : ℝ) * XP‖ + ‖U * X‖ + ‖V * Y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = (t / 2) * ‖XP‖ + ‖U‖ * ‖X‖ + ‖V‖ * ‖Y‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hI, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht (by norm_num))]
      _ ≤ ‖XP‖ / 2 + K * ‖X‖ + K * ‖Y‖ := by
        nlinarith [norm_nonneg XP, mul_le_mul_of_nonneg_right hU (norm_nonneg X),
          mul_le_mul_of_nonneg_right hV (norm_nonneg Y),
          mul_le_mul_of_nonneg_right ht1 (norm_nonneg XP)]
  have hHp := hnorm (-Complex.I) (by simp) F FP A B G hA hB
  have hHm := hnorm Complex.I Complex.norm_I G GP C D F hC hD
  have hreal (X Y : ℂ) : -(star X * Y).re ≤ ‖X‖ * ‖Y‖ := by
    calc
      _ ≤ |(star X * Y).re| := neg_le_abs _
      _ ≤ ‖star X * Y‖ := Complex.abs_re_le_norm _
      _ = ‖X‖ * ‖Y‖ := by rw [norm_mul, norm_star]
  have hp := (hreal F _).trans (mul_le_mul_of_nonneg_left hHp (norm_nonneg F))
  have hm := (hreal G _).trans (mul_le_mul_of_nonneg_left hHm (norm_nonneg G))
  nlinarith [sq_nonneg (‖FP‖ - ‖F‖), sq_nonneg (‖GP‖ - ‖G‖),
    mul_nonneg hK (sq_nonneg (‖F‖ - ‖G‖)), sq_nonneg ‖F‖, sq_nonneg ‖G‖]

theorem homogeneousRegular_coupled_zero (R eta K : ℝ)
    (hR : 0 < R) (hR1 : R ≤ 1) (heta : 0 ≤ eta) (hK : 0 ≤ K)
    (hsmall : (2 * K + 1) * R ^ 2 < 8)
    (A B C D F G : ℝ → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hFR : F R = 0) (hGR : G R = 0)
    (hcoeff : ∀ r ∈ Icc 0 R, ‖A r‖ ≤ K ∧ ‖B r‖ ≤ K ∧ ‖C r‖ ≤ K ∧ ‖D r‖ ≤ K)
    (hODEF : ∀ r, 0 < r → r ≤ R → deriv (deriv F) r +
      ((11 / r : ℝ) : ℂ) * deriv F r - ((eta / r ^ 2 : ℝ) : ℂ) * F r =
      -Complex.I * (r / 2 : ℝ) * deriv F r + A r * F r + B r * G r)
    (hODEG : ∀ r, 0 < r → r ≤ R → deriv (deriv G) r +
      ((11 / r : ℝ) : ℂ) * deriv G r - ((eta / r ^ 2 : ℝ) : ℂ) * G r =
      Complex.I * (r / 2 : ℝ) * deriv G r + C r * G r + D r * F r) :
    ∀ r ∈ Icc 0 R, F r = 0 ∧ G r = 0 := by
  let H := fun r => -Complex.I * (r / 2 : ℝ) * deriv F r + A r * F r + B r * G r
  let J := fun r => Complex.I * (r / 2 : ℝ) * deriv G r + C r * G r + D r * F r
  have hfd := hF.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hgd := hG.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hH : Continuous H := by dsimp only [H]; fun_prop
  have hJ : Continuous J := by dsimp only [J]; fun_prop
  apply homogeneousRegular_pair_zero_of_bound R eta (2 * K + 1) hR heta
    (by positivity) hsmall F G H J hF hG hH hJ hFR hGR hODEF hODEG
  intro r hr
  obtain ⟨hAr, hBr, hCr, hDr⟩ := hcoeff r hr
  exact homogeneousRegular_coupling_bound (A r) (B r) (C r) (D r)
    (F r) (G r) (deriv F r) (deriv G r) r K hr.1 (hr.2.trans hR1) hK hAr hBr hCr hDr

end DefocusingNLS

end OAI
