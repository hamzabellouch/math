import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.MertensHarmonicBands

namespace OAI

/-! # The bounded second Mertens estimate from the first

Only bounded error is needed in the Ostmann application. Partial summation
therefore makes the second prime-sum input a consequence of the first.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

theorem MertensEstimate.floor_error {C : ℝ} (hM : MertensEstimate C)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t| ≤
      C + Real.log 2 := by
  have hf : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hf0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
  have ht0 : 0 < t := by linarith
  have hhalf : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor t
    linarith
  have hlo := Real.log_le_log (show 0 < t / 2 by positivity) hhalf
  rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlo
  have hhi := Real.log_le_log hf0 (Nat.floor_le ht0.le)
  have hM' := abs_le.mp (hM _ hf)
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

private noncomputable def logPrimeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / n else 0

private theorem sum_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  rfl

private theorem sum_inv_log_mul_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, (Real.log (n : ℝ))⁻¹ * logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹ := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [logPrimeCoefficient, hp, ↓reduceIte]
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp
  · simp [logPrimeCoefficient, hp]

private theorem inv_log_differentiable {t : ℝ} (ht : 1 < t) :
    DifferentiableAt ℝ (fun x : ℝ => (Real.log x)⁻¹) t := by
  exact (Real.differentiableAt_log (by linarith)).inv (Real.log_pos ht).ne'

private theorem inv_log_deriv_continuous (Q : ℕ) :
    ContinuousOn (deriv (fun x : ℝ => (Real.log x)⁻¹)) (Set.Icc 2 Q) := by
  simp only [Real.deriv_inv_log]
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

/-- Partial summation for precisely the two prime weights used downstream. -/
theorem prime_reciprocal_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) =
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) / Real.log Q +
      ∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2) := by
  have hid := sum_mul_eq_sub_integral_mul₁ logPrimeCoefficient
    (by norm_num [logPrimeCoefficient]) (by norm_num [logPrimeCoefficient]) (Q : ℝ)
    (f := fun x : ℝ => (Real.log x)⁻¹)
    (fun t ht => inv_log_differentiable (by linarith [ht.1]))
    (inv_log_deriv_continuous Q).integrableOn_Icc
  rw [Nat.floor_natCast, sum_inv_log_mul_logPrimeCoefficient,
    sum_logPrimeCoefficient] at hid
  simp_rw [Real.deriv_inv_log, sum_logPrimeCoefficient] at hid
  rw [← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)] at hid
  have hfun : (fun t : ℝ => -t⁻¹ / Real.log t ^ 2 *
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) =
      fun t : ℝ => -((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_neg] at hid
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hid

private theorem mertens_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_weighted_sum_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have h := integrableOn_mul_sum_Icc logPrimeCoefficient (m := 0)
    (show (0 : ℝ) ≤ 2 by norm_num) (mertens_kernel_continuous Q).integrableOn_Icc
  simpa only [sum_logPrimeCoefficient, mul_comm] using h

private theorem mertens_log_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => Real.log t * (t⁻¹ / Real.log t ^ 2))
      (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_log_kernel_integral (Q : ℕ) (hQ : 2 ≤ Q) :
    (∫ t in (2 : ℝ)..Q, Real.log t * (t⁻¹ / Real.log t ^ 2)) =
      Real.log (Real.log Q) - Real.log (Real.log 2) := by
  rw [← integral_inv_div_log (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : 2 ≤ t := (Set.uIcc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ) ▸ ht).1
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp

private theorem mertens_error_integral_bound {C : ℝ} (hM : MertensEstimate C)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)| ≤ (C + Real.log 2) / Real.log 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hD : 0 ≤ C + Real.log 2 := add_nonneg hC (Real.log_nonneg (by norm_num))
  have hk : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_kernel_continuous Q).integrableOn_Icc
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have he : IntervalIntegrable (fun t : ℝ =>
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    simpa only [sub_mul] using (mertens_weighted_sum_integrable Q hQ).sub hl
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q,
        |((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
          (t⁻¹ / Real.log t ^ 2)| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR (f := fun t : ℝ =>
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)))
    _ ≤ ∫ t in (2 : ℝ)..Q, (C + Real.log 2) * (t⁻¹ / Real.log t ^ 2) := by
      apply intervalIntegral.integral_mono_on hQR he.norm (hk.const_mul _)
      intro t ht
      have hk0 : 0 ≤ t⁻¹ / Real.log t ^ 2 :=
        div_nonneg (inv_nonneg.mpr (by linarith [ht.1])) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_right (hM.floor_error ht.1) hk0
    _ = (C + Real.log 2) * ((Real.log 2)⁻¹ - (Real.log Q)⁻¹) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_div_log_sq (by norm_num : (1 : ℝ) < 2)
          (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
    _ ≤ (C + Real.log 2) / Real.log 2 := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hD
      have : 0 ≤ (Real.log (Q : ℝ))⁻¹ :=
        inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
      linarith

/-- The bounded-error second theorem follows from the first; no second
independent Mertens hypothesis is needed by the conditional main theorem. -/
theorem MertensEstimate.harmonic {C : ℝ} (hM : MertensEstimate C) :
    MertensHarmonicEstimate
      (|1 - Real.log (Real.log 2)| + (2 * C + Real.log 2) / Real.log 2) := by
  intro Q hQ
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlogle : Real.log 2 ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) hQR
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have hei : (∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2)) -
        (Real.log (Real.log Q) - Real.log (Real.log 2)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (mertens_weighted_sum_integrable Q hQ) hl,
      mertens_log_kernel_integral Q hQ]
  have hid : (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) - Real.log (Real.log Q) =
      (1 - Real.log (Real.log 2)) +
        ((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q +
        (∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)) := by
    rw [hei, prime_reciprocal_partial_summation Q hQ]
    field_simp
    ring
  have hendpoint : |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) -
      Real.log Q) / Real.log Q| ≤ C / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogQ]
    exact (div_le_div_of_nonneg_right (hM Q (by omega)) hlogQ.le).trans
      (div_le_div_of_nonneg_left hC hlog2 hlogle)
  rw [hid]
  calc
    _ ≤ |1 - Real.log (Real.log 2)| +
        |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q| +
        |∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)| := (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |1 - Real.log (Real.log 2)| + C / Real.log 2 +
        (C + Real.log 2) / Real.log 2 := by
      exact add_le_add (add_le_add le_rfl hendpoint)
        (mertens_error_integral_bound hM Q hQ)
    _ = _ := by ring

end Ostmann

end OAI
