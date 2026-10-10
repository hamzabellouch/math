import OAI.NumberTheory.EgyptianFractions.FirstDerivativeSum

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeAnalysis

/-- Finite Abel summation controlled by initial partial sums and total variation. -/
theorem weighted_sum_norm_le_partial_sum_bound
    (a b : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n + 1, ‖∑ j ∈ Finset.range k, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (n + 1), b j * a j‖ ≤
      B * (‖b n‖ + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖) := by
  let A : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, a j
  have hdiff (j : ℕ) : A (j + 1) - A j = a j := by
    simp [A, Finset.sum_range_succ]
  have hid := Problem337.weighted_difference_sum A b n
  simp only [hdiff, A, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero] at hid
  rw [hid]
  calc
    _ ≤ ‖b n * ∑ j ∈ Finset.range (n + 1), a j‖ +
        ‖∑ j ∈ Finset.range n, (b (j + 1) - b j) *
          ∑ i ∈ Finset.range (j + 1), a i‖ := norm_sub_le _ _
    _ ≤ ‖b n‖ * B + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The unit exponential is one-Lipschitz in its real angle. -/
theorem norm_exp_I_mul_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤
      |x - y| := by
  have hid : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Linear-phase Abel transfer, uniform in the initial angle and frequency. -/
theorem linear_phase_sum_norm_le
    (a : ℕ → ℂ) (N : ℕ) (B α t : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.range k, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range N,
      Complex.exp (Complex.I * ((α + t * j : ℝ) : ℂ)) * a j‖ ≤
        B * (1 + |t| * N) := by
  cases N with
  | zero => simpa using hB
  | succ n =>
    have h := weighted_sum_norm_le_partial_sum_bound a
      (fun j => Complex.exp (Complex.I * ((α + t * j : ℝ) : ℂ))) n B hprefix
    have hvariation :
        (∑ j ∈ Finset.range n,
          ‖Complex.exp (Complex.I * ((α + t * (j + 1 : ℕ) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((α + t * j : ℝ) : ℂ))‖) ≤ (n : ℝ) * |t| := by
      calc
        _ ≤ ∑ _j ∈ Finset.range n, |t| := by
          apply Finset.sum_le_sum
          intro j hj
          have heq : α + t * (j + 1 : ℕ) - (α + t * j) = t := by
            push_cast
            ring
          simpa only [heq] using norm_exp_I_mul_sub_le
            (α + t * (j + 1 : ℕ)) (α + t * j)
        _ = _ := by simp
    rw [Complex.norm_exp_I_mul_ofReal] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hB
    have ht := abs_nonneg t
    push_cast at hvariation ⊢
    nlinarith

/-- The major-arc partial-summation error estimate, in turns rather than radians.
It is conditional only on the stated finite prefix discrepancy. -/
theorem twisted_sum_sub_norm_le
    (a b : ℕ → ℂ) (N : ℕ) (B β : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ k ≤ N,
      ‖(∑ j ∈ Finset.range k, a j) - ∑ j ∈ Finset.range k, b j‖ ≤ B) :
    ‖(∑ j ∈ Finset.range N,
        Complex.exp (Complex.I * ((2 * Real.pi * β * j : ℝ) : ℂ)) * a j) -
      ∑ j ∈ Finset.range N,
        Complex.exp (Complex.I * ((2 * Real.pi * β * j : ℝ) : ℂ)) * b j‖ ≤
      B * (1 + 2 * Real.pi * |β| * N) := by
  have h := linear_phase_sum_norm_le (fun j => a j - b j) N B 0
    (2 * Real.pi * β) hB (by
      intro k hk
      simpa only [Finset.sum_sub_distrib] using hprefix k hk)
  simpa only [zero_add, mul_sub, Finset.sum_sub_distrib, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using h

end Problem337.ThreePrimeAnalysis

end

end OAI
