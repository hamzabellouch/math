import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # A bounded resolvent estimate for separated spectral cuts

The estimate uses a right inverse only on one spectral subspace. All
operators in the proof are bounded; the later spectral representation
provides these identities for the resolvents of the modular operators.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem norm_separated_cuts_le
    (A B P Q R : H →L[ℂ] H) {e b r : ℝ}
    (he : 0 ≤ e) (hb : 0 ≤ b) (_hr : 0 ≤ r)
    (hcontract : b * r < 1)
    (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ r)
    (hQB : ‖Q * B‖ ≤ b) (hAB : ‖A - B‖ ≤ e)
    (hAR : A * R = P) (hPR : P * R = R) (hQBQ : Q * B * Q = Q * B) :
    ‖Q * P‖ ≤ e * r / (1 - b * r) := by
  have hid : Q * P = Q * (A - B) * R + (Q * B) * (Q * P) * R := by
    calc
      Q * P = Q * (A * R) := by rw [hAR]
      _ = Q * (A - B) * R + Q * B * R := by noncomm_ring
      _ = Q * (A - B) * R + (Q * B) * (Q * P) * R := by
        rw [← mul_assoc (Q * B) Q P, hQBQ, mul_assoc (Q * B) P R, hPR]
  have hfirst : ‖Q * (A - B) * R‖ ≤ e * r := calc
    _ ≤ (‖Q‖ * ‖A - B‖) * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * e) * r := mul_le_mul
      (mul_le_mul hQ hAB (norm_nonneg _) (by norm_num)) hR (norm_nonneg _) (by positivity)
    _ = e * r := by rw [one_mul]
  have hsecond : ‖(Q * B) * (Q * P) * R‖ ≤ b * ‖Q * P‖ * r := calc
    _ ≤ (‖Q * B‖ * ‖Q * P‖) * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (b * ‖Q * P‖) * r := mul_le_mul
      (mul_le_mul_of_nonneg_right hQB (norm_nonneg _)) hR (norm_nonneg _) (by positivity)
  have hn : ‖Q * P‖ ≤ e * r + b * ‖Q * P‖ * r := by
    conv_lhs => rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  apply (le_div_iff₀ (by linarith : 0 < 1 - b * r)).mpr
  nlinarith

/-- A convenient uniform constant for the resolvent cuts separated by
one unit of logarithmic spectrum. -/
theorem norm_logarithmically_separated_cuts_le
    (A B P Q R : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hQ : ‖Q‖ ≤ 1)
    (hR : ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)))
    (hQB : ‖Q * B‖ ≤ Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))))
    (hAB : ‖A - B‖ ≤ e)
    (hAR : A * R = P) (hPR : P * R = R) (hQBQ : Q * B * Q = Q * B) :
    ‖Q * P‖ ≤ ((1 + Real.exp (-(1 / 2 : ℝ))) /
      (1 - Real.exp (-(1 / 2 : ℝ)))) * e := by
  let q := Real.exp (-(1 / 2 : ℝ))
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hc : (q / (1 + q)) * (1 + q) = q := div_mul_cancel₀ _ (by positivity)
  have h := norm_separated_cuts_le A B P Q R he (by positivity : 0 ≤ q / (1 + q))
    (by positivity : 0 ≤ 1 + q) (by rw [hc]; exact hq1) hQ hR hQB hAB hAR hPR hQBQ
  rw [hc] at h
  exact h.trans_eq (by dsimp [q]; ring)

end

end KadisonKastler

end OAI
