import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OAI.NumberTheory.Catalan.Analysis.MixedSeries
import OAI.NumberTheory.Catalan.Analysis.ZetaIntegral

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real

private theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => sqrt (1 - x ^ 2))
      (-x / sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).sqrt hp.ne' using 1
  norm_num
  ring

private theorem mixedOne_complement_cancel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (-log (1 - sqrt (1 - x ^ 2) ^ 2) /
        (sqrt (1 - x ^ 2) * sqrt (1 - sqrt (1 - x ^ 2) ^ 2))) *
      (-x / sqrt (1 - x ^ 2)) = 2 * log x / (1 - x ^ 2) := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hsq : sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := sq_sqrt hp.le
  have hc : 1 - sqrt (1 - x ^ 2) ^ 2 = x ^ 2 := by rw [hsq]; ring
  rw [hc, sqrt_sq hx.1.le, log_pow]
  norm_num only [Nat.cast_ofNat]
  have hs : sqrt (1 - x ^ 2) ≠ 0 := (sqrt_pos.mpr hp).ne'
  calc
    _ = 2 * log x / sqrt (1 - x ^ 2) ^ 2 := by
      field_simp [hx.1.ne', hs]
    _ = _ := by rw [hsq]

theorem integral_mixedOne_logKernel :
    (∫ t in (0 : ℝ)..1, -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2))) =
      (3 / 2 : ℝ) * zetaSeries 0 0 := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => sqrt (1 - x ^ 2))
    (f' := fun x : ℝ => -x / sqrt (1 - x ^ 2))
    (g := fun t : ℝ => -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)))
    (show Continuous (fun x : ℝ => sqrt (1 - x ^ 2)) by fun_prop).continuousOn
    (by
      intro x hx
      simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hx
      exact hasDerivAt_sqrt_one_sub_sq hx)
    (by
      intro x hx
      simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hx
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.1.le) (sqrt_nonneg _))
  have hleft :
      (∫ x in (0 : ℝ)..1,
        ((fun t : ℝ => -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2))) ∘
          (fun x : ℝ => sqrt (1 - x ^ 2))) x *
          (-x / sqrt (1 - x ^ 2))) =
        -(3 / 2 : ℝ) * zetaSeries 0 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, -( -2 * log x / (1 - x ^ 2)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp only [Function.comp_apply]
        rw [mixedOne_complement_cancel hx]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_two_oddLogKernel]
        ring
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, sqrt_one, one_pow,
    sub_self, sqrt_zero] at hsub
  rw [hleft, intervalIntegral.integral_symm] at hsub
  linarith

open MeasureTheory Set Real Polynomial
open scoped Interval

theorem mixed_affine_denominator_pos {t s : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < 1 - t * s := by
  by_cases ht0 : 0 ≤ t
  · have hts : t * s ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs.2)]
    linarith [ht.2]
  · have hts : t * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs.1
    linarith

theorem integral_reciprocal_affine {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (ht0 : t ≠ 0) :
    (∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) = -log (1 - t) / t := by
  have hint : IntervalIntegrable (fun s : ℝ => 1 / (1 - t * s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => (mixed_affine_denominator_pos ht hs).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := fun s : ℝ => -log (1 - t * s) / t)
    (f' := fun s : ℝ => 1 / (1 - t * s)) (fun s hs => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hd : 1 - t * s ≠ 0 := (mixed_affine_denominator_pos ht hs).ne'
      have hderiv := ((((hasDerivAt_id s).const_mul t).const_sub 1).log hd).neg.div_const t
      convert hderiv using 1 <;> dsimp
      field_simp) hint
  simpa only [mul_one, mul_zero, sub_zero, log_one, neg_zero, zero_div] using h

theorem intervalIntegrable_mixedMoment_outer (i j : ℕ) :
    IntervalIntegrable (fun t : ℝ => ∫ s in (0 : ℝ)..1,
      (|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) volume (-1) 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mpr
  change Integrable (fun t : ℝ => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s))
      (volume.restrict (Ioo (-1 : ℝ) 1))
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo]
  exact (integrable_mixedKernel i j).integral_prod_left

theorem integral_mixedZeroLogKernel :
    (∫ t in (0 : ℝ)..1, log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2)) =
      4 * catalan := by
  let f : ℝ → ℝ := fun x => (1 - x ^ 2) / (1 + x ^ 2)
  let f' : ℝ → ℝ := fun x => -4 * x / (1 + x ^ 2) ^ 2
  let g : ℝ → ℝ := fun t => log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2)
  have hf : Continuous f :=
    (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have hderiv (x : ℝ) : HasDerivAt f (f' x) x := by
    have h := ((hasDerivAt_pow 2 x).const_sub 1).div
      ((hasDerivAt_pow 2 x).const_add 1) (by positivity : 1 + x ^ 2 ≠ 0)
    convert h using 1
    dsimp [f, f']
    ring
  have hneg (x : ℝ) (hx : x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) :
      f' x ≤ 0 := by
    have hx0 : 0 ≤ x := by simpa using hx.1.le
    dsimp only [f']
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1) (g := g) hf.continuousOn
    (fun x _ => hderiv x) hneg
  have hpoint (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      g (f x) * f' x = -4 * (-log x / (1 + x ^ 2)) := by
    have hx0 : x ≠ 0 := hx.1.ne'
    have hd : 1 + x ^ 2 ≠ 0 := by positivity
    have hp : 1 + f x = 2 / (1 + x ^ 2) := by
      dsimp only [f]
      field_simp
      ring
    have hm : 1 - f x = 2 * x ^ 2 / (1 + x ^ 2) := by
      dsimp only [f]
      field_simp
      ring
    have hr : (1 + f x) / (1 - f x) = 1 / x ^ 2 := by
      rw [hp, hm]
      field_simp
    have hs : 1 - f x ^ 2 = (2 * x / (1 + x ^ 2)) ^ 2 := by
      dsimp only [f]
      field_simp
      ring
    dsimp only [g, f']
    rw [hr, hs, sqrt_sq (div_nonneg (mul_nonneg (by norm_num) hx.1.le) (by positivity)),
      log_div one_ne_zero (pow_ne_zero 2 hx0), log_one, log_pow]
    field_simp
    ring
  have hi : (∫ x in (0 : ℝ)..1, g (f x) * f' x) = -4 * catalan := by
    calc
      _ = ∫ x in (0 : ℝ)..1, -4 * (-log x / (1 + x ^ 2)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        exact hpoint
      _ = -4 * catalan := by
        rw [intervalIntegral.integral_const_mul, integral_catalanLogKernel]
  have he : (∫ x in (0 : ℝ)..1, g (f x) * f' x) = -(∫ t in (0 : ℝ)..1, g t) := by
    simpa only [Function.comp_apply, f, zero_pow (by decide : 2 ≠ 0), one_pow,
      sub_zero, add_zero, div_one, sub_self, zero_div,
      intervalIntegral.integral_symm (a := (0 : ℝ)) (b := 1)] using hsub
  change (∫ t in (0 : ℝ)..1, g t) = 4 * catalan
  linarith

theorem mixedMoment_zero_zero_eq_log_integral :
    mixedMoment (X ^ 0) (X ^ 0) =
      ∫ t in (0 : ℝ)..1, log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2) := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) / (1 - t * s)
  have hint : IntervalIntegrable F volume (-1) 1 := by
    simpa only [F, pow_zero, one_mul, mul_one] using intervalIntegrable_mixedMoment_outer 0 0
  have h0 : (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by norm_num
  obtain ⟨hn, hp⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hnr : IntervalIntegrable (fun t => F (-t)) volume 0 1 := by
    simpa only [zero_sub, sub_zero, neg_neg] using (hn.comp_sub_left 0).symm
  have hinner {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (ht0 : t ≠ 0) :
      F t = (|t| / sqrt (1 - t ^ 2)) * (-log (1 - t) / t) := by
    calc
      F t = (|t| / sqrt (1 - t ^ 2)) * (∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) := by
        simp only [F, div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_reciprocal_affine ht ht0]
  have hpair {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      F (-t) + F t = log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2) := by
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hnt : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := ht.1.ne'
    have hp0 : 1 + t ≠ 0 := by linarith [ht.1]
    have hm0 : 1 - t ≠ 0 := by linarith [ht.2]
    have hs0 : sqrt (1 - t ^ 2) ≠ 0 := (sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'
    rw [hinner hnt (neg_ne_zero.mpr ht0), hinner ht' ht0,
      abs_neg, abs_of_pos ht.1, neg_sq, sub_neg_eq_add, log_div hp0 hm0]
    field_simp
    ring
  simp only [mixedMoment, pow_zero, Polynomial.eval_one, mul_one]
  change (∫ t in (-1 : ℝ)..1, F t) = _
  calc
    _ = (∫ t in (-1 : ℝ)..0, F t) + ∫ t in (0 : ℝ)..1, F t :=
      (intervalIntegral.integral_add_adjacent_intervals hn hp).symm
    _ = (∫ t in (0 : ℝ)..1, F (-t)) + ∫ t in (0 : ℝ)..1, F t := by
      rw [intervalIntegral.integral_comp_neg]
      norm_num
    _ = ∫ t in (0 : ℝ)..1, F (-t) + F t :=
      (intervalIntegral.integral_add hnr hp).symm
    _ = _ := intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun t ht => hpair ht)

theorem mixedMoment_zero_zero : mixedMoment (X ^ 0) (X ^ 0) = 4 * catalan :=
  mixedMoment_zero_zero_eq_log_integral.trans integral_mixedZeroLogKernel

open MeasureTheory Set Real Polynomial
open scoped Interval

theorem integral_s_reciprocal_affine {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (ht0 : t ≠ 0) :
    (∫ s in (0 : ℝ)..1, s / (1 - t * s)) = (-log (1 - t) - t) / t ^ 2 := by
  have hint : IntervalIntegrable (fun s : ℝ => 1 / (1 - t * s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => (mixed_affine_denominator_pos ht hs).ne')
  calc
    _ = ∫ s in (0 : ℝ)..1, (1 / t) * (1 / (1 - t * s) - 1) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hd : 1 - t * s ≠ 0 := (mixed_affine_denominator_pos ht hs).ne'
      have hd' : 1 - s * t ≠ 0 := by simpa only [mul_comm] using hd
      field_simp [ht0, hd, hd']
      ring
    _ = (1 / t) * ((∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) - 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
      simp
    _ = _ := by
      rw [integral_reciprocal_affine ht ht0]
      field_simp

theorem mixedMoment_zero_one_eq_log_integral :
    mixedMoment (X ^ 0) (X ^ 1) =
      ∫ t in (0 : ℝ)..1, -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)) := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) * s / (1 - t * s)
  have hint : IntervalIntegrable F volume (-1) 1 := by
    simpa only [F, pow_zero, pow_one, one_mul] using intervalIntegrable_mixedMoment_outer 0 1
  have h0 : (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by norm_num
  obtain ⟨hn, hp⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hnr : IntervalIntegrable (fun t => F (-t)) volume 0 1 := by
    simpa only [zero_sub, sub_zero, neg_neg] using (hn.comp_sub_left 0).symm
  have hinner {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (ht0 : t ≠ 0) :
      F t = (|t| / sqrt (1 - t ^ 2)) * ((-log (1 - t) - t) / t ^ 2) := by
    calc
      F t = (|t| / sqrt (1 - t ^ 2)) *
          (∫ s in (0 : ℝ)..1, s / (1 - t * s)) := by
        simp only [F, div_eq_mul_inv, mul_assoc, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_s_reciprocal_affine ht ht0]
  have hpair {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      F (-t) + F t = -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)) := by
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hnt : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := ht.1.ne'
    have hp0 : 1 + t ≠ 0 := by linarith [ht.1]
    have hm0 : 1 - t ≠ 0 := by linarith [ht.2]
    have hs0 : sqrt (1 - t ^ 2) ≠ 0 :=
      (sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'
    have hlog : log (1 - t ^ 2) = log (1 + t) + log (1 - t) := by
      rw [show 1 - t ^ 2 = (1 + t) * (1 - t) by ring, log_mul hp0 hm0]
    rw [hinner hnt (neg_ne_zero.mpr ht0), hinner ht' ht0,
      abs_neg, abs_of_pos ht.1, neg_sq, sub_neg_eq_add, hlog]
    field_simp
    ring_nf
  simp only [mixedMoment, Polynomial.eval_X, Polynomial.eval_one,
    pow_zero, pow_one, one_mul]
  change (∫ t in (-1 : ℝ)..1, F t) = _
  calc
    _ = (∫ t in (-1 : ℝ)..0, F t) + ∫ t in (0 : ℝ)..1, F t :=
      (intervalIntegral.integral_add_adjacent_intervals hn hp).symm
    _ = (∫ t in (0 : ℝ)..1, F (-t)) + ∫ t in (0 : ℝ)..1, F t := by
      rw [intervalIntegral.integral_comp_neg]
      norm_num
    _ = ∫ t in (0 : ℝ)..1, F (-t) + F t :=
      (intervalIntegral.integral_add hnr hp).symm
    _ = _ := intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun t ht => hpair ht)

theorem mixedMoment_zero_one :
    mixedMoment (X ^ 0) (X ^ 1) = (3 / 2 : ℝ) * zetaSeries 0 0 :=
  mixedMoment_zero_one_eq_log_integral.trans integral_mixedOne_logKernel

end InternalCatalan

end

end OAI
