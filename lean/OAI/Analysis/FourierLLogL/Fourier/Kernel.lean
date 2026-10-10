import OAI.Analysis.FourierLLogL.Fourier.Kappa
/-! # Hilbert kernel comparison -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

def kernel (δ t : ℝ) : ℝ := ∫ r in Ico δ 1, kappa (t/r) / r^2

lemma kernel_measurable (δ) : Measurable (kernel δ) := by
  refine StronglyMeasurable.measurable ?_
  unfold kernel
  refine StronglyMeasurable.integral_prod_right (Measurable.stronglyMeasurable ?_)
  exact (kappa_cont.measurable.comp
    (measurable_fst.div measurable_snd)).div (measurable_snd.pow_const 2)

lemma kernel_neg (δ t : ℝ) : kernel δ (-t) = - kernel δ t := by
  unfold kernel
  simp_rw [neg_div, kappa_neg, neg_div, integral_neg]

private lemma recip_deriv (t x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun r : ℝ => t/r) (-t/x^2) x := by
  have h := (hasDerivAt_const x t).div (hasDerivAt_id' x) hx
  simp only [zero_mul, mul_one, zero_sub] at h
  exact h

private lemma recip_cont {δ : ℝ} (hd : 0 < δ) (hb : δ ≤ 1) (t : ℝ) :
    ContinuousOn (fun r : ℝ => -t / r^2) (uIcc δ 1) := by
  rw [uIcc_of_le hb]
  exact continuousOn_const.div (continuousOn_id.pow 2)
    (fun x hx => pow_ne_zero _ (hd.trans_le hx.1).ne')

lemma kernel_small {δ : ℝ} (hd : 0 < δ) (hb : δ ≤ 1) (t : ℝ) :
    |kernel δ t| ≤ 2 / δ := by
  have nn (x : ℝ) (hx : x ∈ uIcc δ 1) : x ≠ 0 :=
    (hd.trans_le ((show x ∈ Icc δ 1 by rwa [uIcc_of_le hb] at hx).1)).ne'
  have hc : ContinuousOn (fun r : ℝ => kappa (t/r) / r^2) (uIcc δ 1) :=
    (kappa_cont.comp_continuousOn (continuousOn_const.div continuousOn_id nn)).div
      (continuousOn_id.pow 2) (fun x hx => pow_ne_zero _ (nn x hx))
  have hI :
      ∀ c : ℝ, (∫ r in δ..1, -c / r^2) = c/1 - c/δ := fun c =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => recip_deriv c x (nn x hx))
      (recip_cont hd hb c).intervalIntegrable
  unfold kernel
  rw [seg_eq_interval _ hb, abs_le]
  constructor
  · apply le_trans (b := ∫ r in δ..1, -(2:ℝ) / r^2) ?_
      (intervalIntegral.integral_mono_on hb (recip_cont hd hb _).intervalIntegrable
        hc.intervalIntegrable (fun x _ => div_le_div_of_nonneg_right
          (abs_le.mp (kappa_bound _)).1 (sq_nonneg x)))
    rw [hI]; linarith
  · have h := intervalIntegral.integral_mono_on (μ:=volume) hb hc.intervalIntegrable
      (recip_cont hd hb (-2)).intervalIntegrable (fun x _ => by
        exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp (kappa_bound (t/x))).2]) (sq_nonneg x))
    refine h.trans ?_
    rw [hI]
    simp
    ring_nf
    norm_num

lemma kernel_middle_id {t δ : ℝ} (hd : 0 < δ) (ht : δ ≤ t) (hb : t ≤ 1) :
    t * kernel δ t = constK - ∫ x in (0:ℝ)..t, kappa x := by
  have hb' := ht.trans hb
  have heq := intervalIntegral.integral_comp_mul_deriv (a:=δ) (b:=1) (fun x hx =>
    recip_deriv t x ((hd.trans_le
      ((show x ∈ Icc δ 1 by rwa [uIcc_of_le hb'] at hx).1)).ne'))
    (recip_cont hd hb' t) kappa_cont
  simp only [Function.comp_apply, div_one] at heq
  have H1 : (-t)* kernel δ t = ∫ x in t/δ..t, kappa x := by
    rw [← heq, kernel, seg_eq_interval _ hb', ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change -t * (_ / x^2) = _ * (-t / x^2)
    ring
  have hI : (∫ x in 1..t/δ, kappa x) = 0 := by
    have hg : (1:ℝ) ≤ t / δ := (le_div_iff₀ hd).mpr (by simpa)
    rw [← seg_eq_interval kappa hg]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      kappa_outside x (hx.1.trans (le_abs_self _))
  have hK := kappa_integral
  rw [seg_eq_interval _ (by norm_num)] at hK
  rw [intervalIntegral.integral_symm] at H1
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (kappa_cont.intervalIntegrable 0 t (μ:=volume)) (kappa_cont.intervalIntegrable t 1)
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (kappa_cont.intervalIntegrable t 1 (μ:=volume)) (kappa_cont.intervalIntegrable 1 (t/δ))
  linarith

lemma kernel_middle_pos {t δ : ℝ} (hd : 0 < δ) (ht : δ ≤ t) (hb : t ≤ 1) :
    |kernel δ t - constK / t| ≤ 2 := by
  have hp := hd.trans_le ht
  have hid := kernel_middle_id hd ht hb
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=t) (fun x _ => show ‖kappa x‖ ≤ 2 from kappa_bound x)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hp, abs_le] at hh
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le]
    field_simp
    nlinarith [hh.2]
  · rw [sub_le_iff_le_add]
    field_simp
    nlinarith [hh.1]

lemma kernel_middle {t δ : ℝ} (hd : 0 < δ) (ht : δ ≤ |t|) (hb : |t| ≤ 1) :
    |kernel δ t - constK / t| ≤ 2 := by
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h] at ht hb; exact kernel_middle_pos hd ht hb
  · rw [abs_of_nonpos h] at ht hb
    have H := kernel_middle_pos hd ht hb
    rw [kernel_neg, div_neg, show -kernel δ t - -(constK / t) = -(kernel δ t - constK / t) by ring, abs_neg] at H
    exact H

end
end FourierLLogL.Period

end OAI
