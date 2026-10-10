import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.Construction.TransferIteration

namespace OAI

/-! # The amplitude reserve with the actual, varying transfer losses -/

namespace Ostmann

open scoped BigOperators

private theorem half_sq_exp (d q : ℝ) :
    Real.exp (-d) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-d + 2 * -q - Real.log 2) := by
  rw [← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add,
    Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Summing the actual losses before using the geometric reserve avoids a
uniform per-step loss assumption. The endpoint is finite, as in the paper. -/
theorem variable_transfer_iteration (k : ℕ) (η : ℕ → ℂ) (diag d : ℕ → ℝ)
    (B₀ m : ℝ) (hm : 0 ≤ m) (hd : ∀ j < k, 0 ≤ d j)
    (hbudget : ∑ j ∈ Finset.range k, (d j + Real.log 2) ≤ m)
    (hzero : Real.exp (-B₀ * m) ≤ ‖η 0‖)
    (hdiag : ∀ j < k, diag j ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m))
    (htransfer : ∀ j < k, Real.exp (-d j) * ‖η j‖ ^ 2 ≤ diag j + ‖η (j + 1)‖) :
    ∀ j ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ j * m) ≤ ‖η j‖ := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum (j : ℕ) (hj : j ≤ k) :
      ∑ h ∈ Finset.range j, (d h + Real.log 2) ≤ m := by
    apply le_trans _ hbudget
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i hi _ => add_nonneg (hd i (Finset.mem_range.mp hi)) hlog)
  have hfine : ∀ j ≤ k,
      Real.exp (-((2 : ℝ) ^ j * (B₀ * m + ∑ h ∈ Finset.range j, (d h + Real.log 2)))) ≤ ‖η j‖ := by
    intro j
    induction j with
    | zero => intro _; simpa using hzero
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hjle : j ≤ k := by omega
      have hprev := ih hjle
      have hcoarse : Real.exp (-(B₀ + 1) * ((2 : ℝ) ^ j * m)) ≤ ‖η j‖ := by
        apply le_trans (Real.exp_le_exp.mpr ?_) hprev
        have hs := mul_le_mul_of_nonneg_left (hsum j hjle) (show 0 ≤ (2 : ℝ) ^ j by positivity)
        nlinarith
      have hloss : d j + Real.log 2 ≤ m := by
        apply le_trans _ (hsum (j + 1) hj)
        have hnonneg : 0 ≤ ∑ h ∈ Finset.range j, (d h + Real.log 2) :=
          Finset.sum_nonneg fun h hh => add_nonneg (hd h (lt_of_lt_of_le (Finset.mem_range.mp hh) hjle)) hlog
        rw [Finset.sum_range_succ]
        linarith
      have ht : 0 ≤ (2 : ℝ) ^ j * m := by positivity
      have htbig : m ≤ (2 : ℝ) ^ j * m := le_mul_of_one_le_left hm (one_le_pow₀ (by norm_num))
      have hhalf := transfer_half_lower ‖η j‖ ‖η (j + 1)‖ (diag j) (B₀ + 1)
        ((2 : ℝ) ^ j * m) (d j) ht (hloss.trans htbig) hcoarse
        (by simpa only [mul_assoc] using hdiag j hjk) (htransfer j hjk)
      have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hprev 2
      apply le_trans _ hhalf
      apply le_trans _ (mul_le_mul_of_nonneg_left hpow (by positivity))
      rw [half_sq_exp]
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_range_succ, pow_succ]
      have hscale : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hl0 : 0 ≤ d j + Real.log 2 := add_nonneg (hd j hjk) hlog
      nlinarith
  intro j hj
  apply le_trans (Real.exp_le_exp.mpr ?_) (hfine j hj)
  have hs := mul_le_mul_of_nonneg_left (hsum j hj) (show 0 ≤ (2 : ℝ) ^ j by positivity)
  nlinarith

end Ostmann

end OAI
