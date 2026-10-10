import Mathlib.Analysis.PSeries
import OAI.NumberTheory.Jacobsthal.Primes.PrimeLaw

namespace OAI

namespace Erdos970

section

namespace EulerPrimeLaw

theorem log_excess_le_rpow {p : ℝ} (hp : 2 ≤ p) :
    Real.log p / (p - 1) ^ 2 ≤ 8 * p ^ (-3 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hlog : Real.log p ≤ 2 * p ^ (1 / 2 : ℝ) := by
    convert Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ring
  have hden : p ^ 2 / 4 ≤ (p - 1) ^ 2 := by nlinarith [sq_nonneg (p - 2)]
  calc
    Real.log p / (p - 1) ^ 2 ≤ (2 * p ^ (1 / 2 : ℝ)) / (p - 1) ^ 2 :=
      div_le_div_of_nonneg_right hlog (sq_nonneg _)
    _ ≤ (2 * p ^ (1 / 2 : ℝ)) / (p ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 8 * p ^ (-3 / 2 : ℝ) := by
      rw [show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hp0, Real.rpow_two]
      ring

noncomputable def integerLogMoment (n : ℕ) : ℝ := Real.log (n : ℝ) / ((n : ℝ) - 1) ^ 2

lemma integerLogMoment_nonneg (n : ℕ) : 0 ≤ integerLogMoment n := by
  cases n with
  | zero => simp [integerLogMoment]
  | succ n =>
      apply div_nonneg _ (sq_nonneg _)
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

lemma integerLogMoment_le (n : ℕ) : integerLogMoment n ≤ 8 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num [integerLogMoment]
  · exact log_excess_le_rpow (by exact_mod_cast h)

theorem integerLogMoment_summable : Summable integerLogMoment := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) := by
    apply Real.summable_nat_rpow.mpr
    norm_num
  exact (hs.mul_left 8).of_nonneg_of_le integerLogMoment_nonneg integerLogMoment_le

noncomputable def uniformMomentBound : ℝ := 1 + ∑' n : ℕ, integerLogMoment n

theorem uniformMomentBound_pos : 0 < uniformMomentBound := by
  have h : 0 ≤ ∑' n : ℕ, integerLogMoment n := tsum_nonneg integerLogMoment_nonneg
  unfold uniformMomentBound
  linarith

theorem finite_log_moment_le (E : Finset ℕ) :
    (∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ uniformMomentBound := by
  have h := integerLogMoment_summable.sum_le_tsum E (fun n _ => integerLogMoment_nonneg n)
  change (∑ p ∈ E, integerLogMoment p) ≤ 1 + ∑' n : ℕ, integerLogMoment n
  linarith

theorem finite_expected_log_excess_le (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p) :
    (∑ p ∈ E, ∑' s : Sample, jointMass (p : ℝ) s *
      ((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log (p : ℝ)) ≤
        uniformMomentBound := by
  calc
    _ = ∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact expected_log_excess (by exact_mod_cast hE p hp)
    _ ≤ uniformMomentBound := finite_log_moment_le E

end EulerPrimeLaw

end

end Erdos970

end OAI
