import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A finite integration-by-parts identity with endpoint terms exposed. -/
theorem weighted_difference_sum (a b : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), b j * (a (j + 1) - a j)) =
      b n * a (n + 1) - b 0 * a 0 -
        ∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- The total variation of a real monotone finite sequence is bounded by
twice a uniform absolute-value bound. -/
theorem real_finite_variation_le (f : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ j ≤ n, |f j| ≤ B)
    (hmono : (∀ j < n, f j ≤ f (j + 1)) ∨
      (∀ j < n, f (j + 1) ≤ f j)) :
    (∑ j ∈ Finset.range n, |f (j + 1) - f j|) ≤ 2 * B := by
  have hn := abs_le.mp (hB n le_rfl)
  have hzero := abs_le.mp (hB 0 (Nat.zero_le _))
  rcases hmono with hmono | hanti
  · have heq : (∑ j ∈ Finset.range n, |f (j + 1) - f j|) = f n - f 0 := by
      calc
        _ = ∑ j ∈ Finset.range n, (f (j + 1) - f j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact abs_of_nonneg (sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj)))
        _ = _ := Finset.sum_range_sub f n
    rw [heq]
    linarith
  · have heq : (∑ j ∈ Finset.range n, |f (j + 1) - f j|) = f 0 - f n := by
      calc
        _ = ∑ j ∈ Finset.range n, -(f (j + 1) - f j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact abs_of_nonpos (sub_nonpos.mpr (hanti j (Finset.mem_range.mp hj)))
        _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [heq]
    linarith

/-- Abel cancellation when reciprocal increments lie on a vertical line and
move monotonically along it. This is the algebraic first-derivative test. -/
theorem first_derivative_sum_bound (a b : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (ha : ∀ j ≤ n + 1, ‖a j‖ ≤ 1)
    (hb : ∀ j ≤ n, ‖b j‖ ≤ B)
    (hreal : ∀ j ≤ n, (b j).re = (b 0).re)
    (hmono : (∀ j < n, (b j).im ≤ (b (j + 1)).im) ∨
      (∀ j < n, (b (j + 1)).im ≤ (b j).im))
    (hrel : ∀ j ≤ n, b j * (a (j + 1) - a j) = a j) :
    ‖∑ j ∈ Finset.range (n + 1), a j‖ ≤ 4 * B := by
  have hB : 0 ≤ B := (norm_nonneg (b 0)).trans (hb 0 (Nat.zero_le _))
  have hvar : (∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖) ≤ 2 * B := by
    have heq : (∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖) =
        ∑ j ∈ Finset.range n, |(b (j + 1)).im - (b j).im| := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hre : (b (j + 1) - b j).re = 0 := by
        simp only [Complex.sub_re, hreal (j + 1) (by omega), hreal j (by omega), sub_self]
      simpa only [Complex.sub_im] using (Complex.abs_im_eq_norm.mpr hre).symm
    rw [heq]
    apply real_finite_variation_le (fun j => (b j).im) n B
    · intro j hj
      exact (Complex.abs_im_le_norm _).trans (hb j hj)
    · exact hmono
  have hend (j : ℕ) (hj : j ≤ n) (l : ℕ) (hl : l ≤ n + 1) : ‖b j * a l‖ ≤ B := by
    rw [norm_mul]
    calc
      ‖b j‖ * ‖a l‖ ≤ ‖b j‖ * 1 := mul_le_mul_of_nonneg_left (ha l hl) (norm_nonneg _)
      _ ≤ B := by simpa using hb j hj
  have hsum : (∑ j ∈ Finset.range (n + 1), a j) =
      b n * a (n + 1) - b 0 * a 0 -
        ∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1) := by
    rw [← weighted_difference_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hrel j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)).symm
  rw [hsum]
  calc
    ‖b n * a (n + 1) - b 0 * a 0 - ∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1)‖ ≤
        ‖b n * a (n + 1) - b 0 * a 0‖ + ‖∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1)‖ := norm_sub_le _ _
    _ ≤ (‖b n * a (n + 1)‖ + ‖b 0 * a 0‖) +
        ∑ j ∈ Finset.range n, ‖(b (j + 1) - b j) * a (j + 1)‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ ≤ (B + B) + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖ := by
      apply add_le_add
      · exact add_le_add (hend n le_rfl (n + 1) le_rfl) (hend 0 (Nat.zero_le _) 0 (Nat.zero_le _))
      · apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        have haj := ha (j + 1) (by have := Finset.mem_range.mp hj; omega)
        simpa using mul_le_mul_of_nonneg_left haj (norm_nonneg (b (j + 1) - b j))
    _ ≤ 4 * B := by linarith

end Problem337

end OAI
