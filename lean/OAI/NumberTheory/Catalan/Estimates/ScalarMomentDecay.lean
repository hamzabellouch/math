import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import OAI.NumberTheory.Catalan.Polynomial.CentralCoefficients

namespace OAI

noncomputable section

namespace InternalCatalan

section

open MeasureTheory Set Real
open scoped Interval

def scalarMoment (i : ℕ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, t ^ i * (|t| / Real.sqrt (1 - t ^ 2))

private theorem sine_deriv_nonneg (x : ℝ)
    (hx : x ∈ Ioo (min (-(π / 2)) (π / 2)) (max (-(π / 2)) (π / 2))) :
    0 ≤ cos x := by
  have hp : -(π / 2) ≤ π / 2 := by linarith [pi_pos]
  rw [min_eq_left hp, max_eq_right hp] at hx
  exact (cos_pos_of_mem_Ioo hx).le

private theorem scalar_sine_cancel (i : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    (sin x ^ i * (|sin x| / sqrt (1 - sin x ^ 2))) * cos x =
      sin x ^ i * |sin x| := by
  rw [← cos_eq_sqrt_one_sub_sin_sq hx.1.le hx.2.le]
  have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo hx).ne'
  field_simp

theorem scalarMoment_eq_sine (i : ℕ) :
    scalarMoment i =
      ∫ x in (-(π / 2))..(π / 2), sin x ^ i * |sin x| := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [Function.comp_apply, sin_neg, sin_pi_div_two] at hsub
  unfold scalarMoment
  rw [← hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos])
  intro x hx
  exact scalar_sine_cancel i hx

theorem intervalIntegrable_scalarMoment (i : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
      volume (-1) 1 := by
  have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [sin_neg, sin_pi_div_two] at hsub
  apply hsub.mp
  have hc : Continuous (fun x : ℝ => sin x ^ i * |sin x|) := by fun_prop
  apply (hc.intervalIntegrable (-(π / 2)) (π / 2)).congr_uIoo
  intro x hx
  rw [uIoo_of_le (show -(π / 2) ≤ π / 2 by linarith [pi_pos])] at hx
  exact (scalar_sine_cancel i hx).symm

theorem scalarMoment_integrand_odd (k : ℕ) (t : ℝ) :
    (-t) ^ (2 * k + 1) * (|-t| / Real.sqrt (1 - (-t) ^ 2)) =
      -(t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2))) := by
  simp only [abs_neg, neg_sq, pow_add, pow_mul, pow_one]
  ring

theorem scalarMoment_odd (k : ℕ) : scalarMoment (2 * k + 1) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (fun t : ℝ => t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2)))
  simp only [neg_neg, scalarMoment_integrand_odd, intervalIntegral.integral_neg] at h
  change -scalarMoment (2 * k + 1) = scalarMoment (2 * k + 1) at h
  linarith

theorem scalarMoment_eq_zero_of_odd {i : ℕ} (hi : Odd i) : scalarMoment i = 0 := by
  obtain ⟨k, rfl⟩ := hi
  simpa only [two_mul] using scalarMoment_odd k

private theorem interval_even_double (f : ℝ → ℝ) (hf : Function.Even f) {a : ℝ}
    (hint : IntervalIntegrable f volume (-a) a) (ha : 0 ≤ a) :
    (∫ x in -a..a, f x) = 2 * ∫ x in (0 : ℝ)..a, f x := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (-a) a := by
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)]
    exact ⟨by linarith, ha⟩
  obtain ⟨hl, hr⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hf' (x : ℝ) : f (-x) = f x := hf x
  have hleft : (∫ x in -a..0, f x) = ∫ x in (0 : ℝ)..a, f x := by
    simpa only [hf', neg_zero] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f).symm
  calc
    (∫ x in -a..a, f x) = (∫ x in -a..0, f x) + ∫ x in (0 : ℝ)..a, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hl hr).symm
    _ = 2 * ∫ x in (0 : ℝ)..a, f x := by rw [hleft]; ring

theorem scalarMoment_even_eq_sine (l : ℕ) :
    scalarMoment (2 * l) =
      2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) := by
  rw [scalarMoment_eq_sine]
  have hf : Function.Even (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by
    intro x
    simp only [sin_neg, abs_neg, pow_mul, neg_sq]
  have hc : Continuous (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by fun_prop
  rw [interval_even_double _ hf (hc.intervalIntegrable (-(π / 2)) (π / 2)) (by positivity)]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro x hx
  have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, pi_pos])
  change sin x ^ (2 * l) * |sin x| = sin x ^ (2 * l + 1)
  rw [abs_of_nonneg hs, pow_succ]

theorem two_integral_sine_odd_eq_momentScalar (l : ℕ) :
    2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) =
      (momentScalar (2 * l) : ℝ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have he : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
    have hrec := integral_sin_pow (a := 0) (b := π / 2) (2 * l + 1)
    have hexp : 0 < 2 * l + 1 + 1 := by omega
    simp only [sin_zero, zero_pow (Nat.ne_of_gt hexp), cos_zero, zero_mul,
      sin_pi_div_two, one_pow, cos_pi_div_two, mul_zero, sub_self, zero_div,
      zero_add] at hrec
    rw [he, hrec]
    rw [show 2 * ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2) *
      (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) =
        ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2)) *
          (2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) by ring, ih]
    rw [momentScalar_even, momentScalar_even]
    have hc : (↑(2 * l + 2) : ℝ) * (centralCoeff (l + 1) : ℝ) =
        (↑(2 * l + 1) : ℝ) * (centralCoeff l : ℝ) := by
      exact_mod_cast centralCoeff_step l
    have hc0 : (centralCoeff l : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero l
    have hc1 : (centralCoeff (l + 1) : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero (l + 1)
    push_cast at hc ⊢
    field_simp
    nlinarith only [hc]

theorem scalarMoment_eq_momentScalar (i : ℕ) :
    scalarMoment i = (momentScalar i : ℝ) := by
  rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
  · exact (scalarMoment_even_eq_sine l).trans
      (two_integral_sine_odd_eq_momentScalar l)
  · rw [scalarMoment_odd, momentScalar_odd, Rat.cast_zero]

@[simp] theorem scalarMoment_zero : scalarMoment 0 = 2 := by
  rw [scalarMoment_eq_momentScalar, momentScalar_zero]
  norm_num

end

open MeasureTheory Set Real Filter
open scoped Interval Topology

theorem tendsto_scalarMoment_zero :
    Tendsto scalarMoment atTop (𝓝 0) := by
  have h :
      Tendsto
        (fun n : ℕ => ∫ t in (-1 : ℝ)..1,
          t ^ n * (|t| / Real.sqrt (1 - t ^ 2)))
        atTop (𝓝 (∫ _t in (-1 : ℝ)..1, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => |t| / Real.sqrt (1 - t ^ 2))
    · exact Eventually.of_forall fun n =>
        (intervalIntegrable_scalarMoment n).aestronglyMeasurable_restrict_uIoc
    · refine Eventually.of_forall fun n => Eventually.of_forall ?_
      intro t ht
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hw : 0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
        div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hw]
      exact mul_le_of_le_one_left hw (pow_le_one₀ (abs_nonneg t) ht_abs)
    · simpa only [pow_zero, one_mul] using intervalIntegrable_scalarMoment 0
    · refine Eventually.of_forall ?_
      intro t ht
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      by_cases ht1 : t = 1
      · subst t
        simpa only [one_pow, sub_self, Real.sqrt_zero, abs_one, div_zero, mul_zero]
          using (tendsto_const_nhds :
            Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · have ht_abs : |t| < 1 :=
          abs_lt.mpr ⟨ht.1, (lt_or_eq_of_le ht.2).resolve_right ht1⟩
        simpa only [zero_mul] using
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one ht_abs).mul_const
            (|t| / Real.sqrt (1 - t ^ 2))
  change Tendsto
    (fun n : ℕ => ∫ t in (-1 : ℝ)..1,
      t ^ n * (|t| / Real.sqrt (1 - t ^ 2))) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using h

theorem tendsto_momentScalar_zero :
    Tendsto (fun n : ℕ => (momentScalar n : ℝ)) atTop (𝓝 0) := by
  simpa only [scalarMoment_eq_momentScalar] using
    (show Tendsto (fun n : ℕ => scalarMoment n) atTop (𝓝 0) from
      tendsto_scalarMoment_zero)

end InternalCatalan

end

end OAI
