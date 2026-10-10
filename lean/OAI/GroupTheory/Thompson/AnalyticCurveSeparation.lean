import OAI.GroupTheory.Thompson.AnalyticCurve
import OAI.GroupTheory.Thompson.AnalyticSeparation

namespace OAI

/-!
# Uniform separation of the actual Hilbert-space curve

Every premise of the finite-region separation theorem is proved here from the
literal scalar profiles and the oscillator inner-product identity. In
particular no separation or injectivity property of the curve is assumed.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set

theorem gamma_sub_norm_of_le_one (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1) :
    ‖gamma t - gamma s‖ = (t - s) / 8 := by
  rw [gamma_of_le_one ht, gamma_of_le_one (hst.trans ht), ← sub_smul,
    norm_smul, Real.norm_eq_abs, wave_norm, mul_one]
  have hdiv : t / 8 - s / 8 = (t - s) / 8 := by ring
  rw [hdiv, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) (by norm_num))]

theorem theta_lt_of_lt_of_one_lt {s t : ℝ} (hst : s < t) (ht : 1 < t) :
    theta s < theta t := by
  by_cases hs : s ≤ 1
  · have hstrict := theta_strictMonoOn
      (show (1 : ℝ) ∈ Ici (1 : ℝ) from le_refl (1 : ℝ))
      (show t ∈ Ici (1 : ℝ) from ht.le) ht
    simpa only [theta_of_le_one hs, theta_of_le_one (le_refl (1 : ℝ))] using hstrict
  · exact theta_strictMonoOn (le_of_not_ge hs) ht.le hst

theorem gamma_sub_norm_pos {s t : ℝ} (hst : s < t) : 0 < ‖gamma t - gamma s‖ := by
  by_cases ht : t ≤ 1
  · rw [gamma_sub_norm_of_le_one s t hst.le ht]
    exact div_pos (sub_pos.mpr hst) (by norm_num)
  have ht' : 1 < t := lt_of_not_ge ht
  have ha : 0 < a t := by linarith [a_lower_of_one_le ht'.le]
  have hgap : 0 < theta t - theta s := sub_pos.mpr (theta_lt_of_lt_of_one_lt hst ht')
  have hk : |sinc (theta t - theta s)| < 1 := abs_sinc_lt_one (ne_of_gt hgap)
  have hk2 : sinc (theta t - theta s) ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg (sinc (theta t - theta s)))
      (by norm_num : (0 : ℝ) ≤ 1)).2 hk
    simpa only [sq_abs, one_pow] using h
  have hpositive : 0 < (a t) ^ 2 * (1 - sinc (theta t - theta s) ^ 2) :=
    mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hk2)
  have hnonneg := sq_nonneg (a s - a t * sinc (theta t - theta s))
  have hformula := gamma_sub_norm_sq s t
  have hsq : 0 < ‖gamma t - gamma s‖ ^ 2 := by nlinarith
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hsq))

theorem gamma_injective : Function.Injective gamma := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hpositive := gamma_sub_norm_pos hst
    exact (ne_of_gt hpositive) (by simp only [heq, sub_self, norm_zero])
  · have hpositive := gamma_sub_norm_pos hts
    exact (ne_of_gt hpositive) (by simp only [heq, sub_self, norm_zero])

theorem gamma_sub_norm_ge_of_far_negative (s t : ℝ) (hs : s ≤ -4) (ht : 1 < t) :
    3 / 16 ≤ ‖gamma t - gamma s‖ := by
  have hsbound : (1 / 2 : ℝ) ≤ ‖gamma s‖ := by
    rw [gamma_norm, a_of_le_two (by linarith), abs_of_nonpos (by linarith)]
    linarith
  have htbound : ‖gamma t‖ ≤ 5 / 16 := by
    have hapos : 0 ≤ a t := by linarith [a_lower_of_one_le ht.le]
    rw [gamma_norm, abs_of_nonneg hapos]
    exact a_le_five_sixteenths t
  have hreverse : ‖gamma s‖ - ‖gamma t‖ ≤ ‖gamma t - gamma s‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le (gamma s) (gamma t)
  linarith

theorem gamma_sub_norm_sq_tail (s t : ℝ) (hs : 3 ≤ s) (hst : s ≤ t) :
    ‖gamma t - gamma s‖ ^ 2 = 2 * (5 / 16 : ℝ) ^ 2 * (1 - sinc (t - s)) := by
  rw [gamma_sub_norm_sq, a_of_three_le hs, a_of_three_le (hs.trans hst),
    theta_of_two_le (by linarith : 2 ≤ t), theta_of_two_le (by linarith : 2 ≤ s)]
  have hgap : (t - 3 / 2) - (s - 3 / 2) = t - s := by ring
  rw [hgap]
  ring

theorem gamma_sub_norm_sq_ge_of_cross_tail (s t : ℝ) (hs : s ≤ 3) (ht : 5 ≤ t) :
    3 * (5 / 16 : ℝ) ^ 2 / 4 ≤ ‖gamma t - gamma s‖ ^ 2 := by
  have htheta_s : theta s ≤ 3 / 2 := by
    calc
      theta s ≤ theta 3 := theta_monotone hs
      _ = 3 / 2 := by rw [theta_of_two_le (by norm_num : (2 : ℝ) ≤ 3)]; norm_num
  have htheta_t : 7 / 2 ≤ theta t := by
    rw [theta_of_two_le (by linarith)]
    linarith
  have hgap : 2 ≤ theta t - theta s := by linarith
  have habs := abs_sinc_le_half_of_two_le hgap
  have hklow := (abs_le.mp habs).1
  have hkhi := (abs_le.mp habs).2
  have hproduct : 0 ≤ (sinc (theta t - theta s) + 1 / 2) *
      (1 / 2 - sinc (theta t - theta s)) := mul_nonneg (by linarith) (by linarith)
  have hk2 : sinc (theta t - theta s) ^ 2 ≤ 1 / 4 := by nlinarith
  rw [gamma_sub_norm_sq, a_of_three_le (by linarith : 3 ≤ t)]
  nlinarith [sq_nonneg (a s - (5 / 16 : ℝ) * sinc (theta t - theta s))]

theorem gamma_uniform_separation (d : ℝ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ s t : ℝ, d ≤ |t - s| → η ≤ ‖gamma t - gamma s‖ :=
  uniform_separation_of_five_regions gamma continuous_gamma gamma_injective
    gamma_sub_norm_of_le_one gamma_sub_norm_ge_of_far_negative gamma_sub_norm_sq_tail
    gamma_sub_norm_sq_ge_of_cross_tail d hd

end ThompsonNonamenability.Analytic

end

end OAI
