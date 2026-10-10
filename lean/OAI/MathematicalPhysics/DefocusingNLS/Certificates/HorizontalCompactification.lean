import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardConeMonotonicity

namespace OAI

/-! # The forward recurrence at inverse imaginary frequency zero -/

open Matrix

namespace DefocusingNLS

noncomputable def horizontalDifference (ell n : ℕ) (h σ b Z τ : ℝ) (B C : ℂ) : ℂ :=
  -((τ : ℂ) * ((ell : ℂ) + 5) * B + (h : ℂ) * Complex.I * Z * C) /
    (Complex.I + (τ : ℂ) *
      ((((σ + (ell : ℝ) / 2 + n - ((ell : ℝ) + 5) : ℝ) : ℂ)) -
        (h : ℂ) * Complex.I * b))

noncomputable def horizontalState (ell : ℕ) (h σ b Z τ : ℝ) (B C : ℂ) : ℕ → ℂ × ℂ
  | 0 => (B, C)
  | n + 1 =>
      let bc := horizontalState ell h σ b Z τ B C n
      let B' := bc.1 - horizontalDifference ell n h σ b Z τ bc.1 bc.2
      (B', bc.2 - (τ : ℂ) * B')

theorem horizontalDifference_zero (ell n : ℕ) (h σ b Z : ℝ) (B C : ℂ) :
    horizontalDifference ell n h σ b Z 0 B C = -(h : ℂ) * Z * C := by
  simp only [horizontalDifference, Complex.ofReal_zero, zero_mul, zero_add, add_zero]
  apply (div_eq_iff Complex.I_ne_zero).mpr
  calc
    -((h : ℂ) * Complex.I * Z * C) =
      (-(h : ℂ) * Z * C) * Complex.I := by ring

theorem horizontalState_zero (ell n : ℕ) (h σ b Z : ℝ) (B C : ℂ) :
    horizontalState ell h σ b Z 0 B C n = (B + n * (h : ℂ) * Z * C, C) := by
  induction n with
  | zero => simp [horizontalState]
  | succ n ih =>
    rw [horizontalState, ih, horizontalDifference_zero]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    congr 1
    push_cast
    ring

noncomputable def horizontalIncrementSum (ell : ℕ) (h σ b Z τ : ℝ)
    (B C : ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (σ + n - 5 / 2) * Complex.normSq
    (horizontalDifference ell n h σ b Z τ
      (horizontalState ell h σ b Z τ B C n).1
      (horizontalState ell h σ b Z τ B C n).2)

theorem horizontalIncrementSum_zero (ell N : ℕ) (h σ b Z : ℝ) (B C : ℂ) :
    horizontalIncrementSum ell h σ b Z 0 B C N =
      ((N : ℝ) * σ + (N : ℝ) * (N - 1 : ℝ) / 2 - (N : ℝ) * (5 / 2)) *
        (h ^ 2 * Z ^ 2 * Complex.normSq C) := by
  simp only [horizontalIncrementSum, horizontalState_zero, horizontalDifference_zero]
  have hn : Complex.normSq (-(h : ℂ) * Z * C) = h ^ 2 * Z ^ 2 * Complex.normSq C := by
    simp [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal, pow_two]
  simp only [hn]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The horizontal limiting form is uniformly positive in the counting strip.
No asymptotic assumption is used: this is the exact value at inverse frequency zero. -/
theorem horizontal_limiting_form_pos (ell : ℕ) (σ b Z : ℝ) (B C : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hZ : Z ≠ 0) (hBC : B ≠ 0 ∨ C ≠ 0) :
    0 < ((ell : ℝ) + 5) * Complex.normSq B +
      horizontalIncrementSum ell 1 σ b Z 0 B C 8 +
      horizontalIncrementSum ell (-1) σ b Z 0 B C 8 := by
  rw [horizontalIncrementSum_zero, horizontalIncrementSum_zero]
  norm_num
  have hM : 0 < (ell : ℝ) + 5 := by positivity
  have hcoef : 0 < 8 * σ + 8 := by linarith
  have hZ2 : 0 < Z ^ 2 := sq_pos_of_ne_zero hZ
  rcases hBC with hB | hC
  · have hp := mul_pos hM (Complex.normSq_pos.mpr hB)
    have hn : 0 ≤ (8 * σ + 8) * (Z ^ 2 * Complex.normSq C) :=
      mul_nonneg hcoef.le (mul_nonneg hZ2.le (Complex.normSq_nonneg C))
    nlinarith
  · have hp := mul_pos hcoef (mul_pos hZ2 (Complex.normSq_pos.mpr hC))
    have hn := mul_nonneg hM.le (Complex.normSq_nonneg B)
    nlinarith

end DefocusingNLS

end OAI
