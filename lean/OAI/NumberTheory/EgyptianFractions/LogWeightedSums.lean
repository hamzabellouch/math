import Mathlib

namespace OAI
/-!
# Logarithmic weights in finite exponential sums

Abel summation transfers a uniform bound for all prefixes of a sequence to
its logarithmically weighted sum. This supplies the inner logarithmic weight
in the first Type I term of Vaughan's identity; no estimate over primes is
assumed here.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.Vaughan

/-- An increasing nonnegative real weight costs at most twice its endpoint
when all unweighted prefix sums are bounded by `B`. -/
theorem norm_sum_smul_le_two_mul_of_monotone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ) (z : ℕ → E) (N : ℕ) (B : ℝ)
    (hf : Monotone f) (hf0 : 0 ≤ f 0)
    (hprefix : ∀ k ≤ N + 1, ‖∑ j ∈ Finset.range k, z j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (N + 1), f j • z j‖ ≤ 2 * f N * B := by
  have hB : 0 ≤ B := by simpa using hprefix 0 (Nat.zero_le _)
  have hfN : 0 ≤ f N := hf0.trans (hf (Nat.zero_le _))
  have hdiff (j : ℕ) : 0 ≤ f (j + 1) - f j :=
    sub_nonneg.mpr (hf (Nat.le_succ j))
  have hparts := Finset.sum_range_by_parts f z (N + 1)
  simp only [Nat.add_sub_cancel] at hparts
  rw [hparts]
  calc
    _ ≤ ‖f N • ∑ j ∈ Finset.range (N + 1), z j‖ +
        ‖∑ j ∈ Finset.range N,
          (f (j + 1) - f j) • ∑ i ∈ Finset.range (j + 1), z i‖ := norm_sub_le _ _
    _ ≤ f N * B + ∑ j ∈ Finset.range N, (f (j + 1) - f j) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfN]
        exact mul_le_mul_of_nonneg_left (hprefix _ le_rfl) hfN
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdiff j)]
        exact mul_le_mul_of_nonneg_left
          (hprefix (j + 1) (by have := Finset.mem_range.mp hj; omega)) (hdiff j)
    _ = f N * B + (f N - f 0) * B := by
      rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ ≤ 2 * f N * B := by nlinarith

/-- Logarithmic weights on positive indices, in shifted-range form.
The result also holds for `N = 0` and `N = 1`, when the weighted sum is zero. -/
theorem norm_log_weighted_range_le
    (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.range k, z (j + 1)‖ ≤ B) :
    ‖∑ j ∈ Finset.range N, (Real.log (j + 1 : ℕ) : ℂ) * z (j + 1)‖ ≤
      2 * Real.log N * B := by
  cases N with
  | zero => simp
  | succ N =>
    have hmono : Monotone (fun j : ℕ => Real.log (j + 1 : ℕ)) := by
      intro i j hij
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.add_le_add_right hij 1
    simpa only [Complex.real_smul, Nat.succ_eq_add_one] using
      norm_sum_smul_le_two_mul_of_monotone
        (fun j : ℕ => Real.log (j + 1 : ℕ)) (fun j => z (j + 1)) N B
        hmono (by simp) hprefix

lemma sum_Icc_one_eq_shifted_range {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N, f j) = ∑ j ∈ Finset.range N, f (j + 1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  change (∑ j ∈ Finset.range (N + 1 - 1), f (1 + j)) = _
  simp only [Nat.add_sub_cancel, add_comm 1]

/-- Positive-interval formulation of the logarithmic Abel estimate. -/
theorem norm_log_weighted_Icc_le
    (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.Icc 1 k, z j‖ ≤ B) :
    ‖∑ j ∈ Finset.Icc 1 N, (Real.log j : ℂ) * z j‖ ≤
      2 * Real.log N * B := by
  rw [sum_Icc_one_eq_shifted_range]
  apply norm_log_weighted_range_le
  intro k hk
  simpa only [sum_Icc_one_eq_shifted_range] using hprefix k hk

end Problem337.Vaughan

end

end OAI
