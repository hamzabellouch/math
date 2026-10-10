import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A weighted binomial bound, allowing a real cutoff on subset size. -/
theorem weighted_binomial_bound (L : ℕ) (t q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
      (Nat.choose L j : ℝ)) ≤ q ^ (-t) * (1 + q) ^ L := by
  have hw : q ^ t *
      (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
        (Nat.choose L j : ℝ)) ≤ (1 + q) ^ L := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
          q ^ j * (Nat.choose L j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range (L + 1), q ^ j * (Nat.choose L j : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j hj hnot
        positivity
      _ = (1 + q) ^ L := by
        rw [show 1 + q = q + 1 by ring, add_pow]
        simp
  have hqt : 0 < q ^ t := Real.rpow_pos_of_pos hq0 t
  have hdiv :
      (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
        (Nat.choose L j : ℝ)) ≤ (1 + q) ^ L / q ^ t :=
    (le_div_iff₀ hqt).2 (by simpa only [mul_comm] using hw)
  simpa only [Real.rpow_neg hq0.le, div_eq_mul_inv, mul_comm] using hdiv

/-- Exponential form of the weighted subset count used in divisor estimates. -/
theorem weighted_binomial_exp_bound (L : ℕ) (t q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
      (Nat.choose L j : ℝ)) ≤ Real.exp (-t * Real.log q + (L : ℝ) * q) := by
  apply (weighted_binomial_bound L t q hq0 hq1).trans
  have hqadd : 0 < 1 + q := by positivity
  rw [← Real.rpow_natCast (1 + q) L,
    Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hqadd, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (1 + q) ≤ q := by
    simpa using Real.log_le_sub_one_of_pos hqadd
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

end Problem337

end

end OAI
