import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaCompletion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Quantitative Mellin bounds on the exponentially decaying half of theta. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace CubicFirstMoment

lemma theta_mellin_exponent_bound {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) (s : ℂ) :
    Real.log t * (s.re-1) - c*t ≤
      2*(1+‖s‖)^2/c - (c/2)*t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hl0 := Real.log_nonneg ht
  have hl : Real.log t ≤ 2*Real.sqrt t := by
    have hh := Real.log_le_rpow_div ht0.le (show 0 < (1/2:ℝ) by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hr : s.re-1 ≤ 1+‖s‖ := by linarith [Complex.re_le_norm s]
  have h1 := mul_le_mul_of_nonneg_left hr hl0
  have h2 := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+‖s‖ by positivity)
  have hsq := sq_nonneg (c*Real.sqrt t - 2*(1+‖s‖))
  have hroot := Real.sq_sqrt ht0.le
  have hdiv : c*(2*(1+‖s‖)^2/c) = 2*(1+‖s‖)^2 :=
    mul_div_cancel₀ _ hc.ne'
  have hsq' : 0 ≤ c^2*t-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by
    calc
      0 ≤ (c*Real.sqrt t - 2*(1+‖s‖))^2 := hsq
      _ = c^2*(Real.sqrt t)^2-4*c*(1+‖s‖)*Real.sqrt t+4*(1+‖s‖)^2 := by ring
      _ = _ := by rw [hroot]
  have hy : 2*(1+‖s‖)*Real.sqrt t ≤ c*t/2 + 2*(1+‖s‖)^2/c := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hsq',hdiv]
  nlinarith

lemma theta_mellin_integrand_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t))
    (s : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t:ℂ)^(s-1)*f t‖ ≤
      (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  calc
    _ ≤ t^((s-1).re)*(C*Real.exp (-c*t)) :=
      mul_le_mul_of_nonneg_left (hf t ht) (Real.rpow_nonneg ht0.le _)
    _ = C*Real.exp (Real.log t*(s.re-1)-c*t) := by
      rw [Real.rpow_def_of_pos ht0,Complex.sub_re,Complex.one_re,
        show Real.log t*(s.re-1)-c*t = Real.log t*(s.re-1)+(-c*t) by ring,Real.exp_add]
      ring
    _ ≤ C*Real.exp (2*(1+‖s‖)^2/c-(c/2)*t) := by
      have hC : 0 ≤ C := by
        have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
        exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (theta_mellin_exponent_bound hc ht s)) hC
    _ = _ := by
      rw [show 2*(1+‖s‖)^2/c-(c/2)*t = 2*(1+‖s‖)^2/c+(-(c/2)*t) by ring, Real.exp_add]
      ring

lemma theta_upper_integrable {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*f t) (Ioi 1) := by
  have hg := (integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul
    (C*Real.exp (2*(1+‖s‖)^2/c))
  apply hg.mono' _
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
      theta_mellin_integrand_bound hc hf s ht.le))
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.mul _ (hfcont.mono (Ioi_subset_Ioi (by norm_num)))
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).continuousWithinAt

lemma theta_upper_norm_bound {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t‖ ≤
      (2*C/c)*Real.exp (2*(1+‖s‖)^2/c) := by
  have hC : 0 ≤ C := by
    have hh := (_root_.norm_nonneg (f 1)).trans (hf 1 le_rfl)
    exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
  calc
    _ ≤ ∫ t : ℝ in Ioi 1,
        (C*Real.exp (2*(1+‖s‖)^2/c))*Real.exp (-(c/2)*t) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (show -(c/2) < 0 by linarith) 1).const_mul _)
      exact ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => theta_mellin_integrand_bound hc hf s ht.le)
    _ = (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*Real.exp (-(c/2)) := by
      rw [integral_const_mul,integral_exp_mul_Ioi (show -(c/2) < 0 by linarith)]
      field_simp
    _ ≤ (C*Real.exp (2*(1+‖s‖)^2/c))*(2/c)*1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
