import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalUniformPositivity

namespace OAI

/-! # Removing the unit-vector normalization from the horizontal estimate -/

open Set Metric

namespace DefocusingNLS

theorem horizontalDifference_mul (ell n : ℕ) (h σ b Z τ : ℝ) (a B C : ℂ) :
    horizontalDifference ell n h σ b Z τ (a * B) (a * C) =
      a * horizontalDifference ell n h σ b Z τ B C := by
  unfold horizontalDifference
  ring

theorem horizontalState_mul (ell n : ℕ) (h σ b Z τ : ℝ) (a B C : ℂ) :
    horizontalState ell h σ b Z τ (a * B) (a * C) n =
      (a * (horizontalState ell h σ b Z τ B C n).1,
       a * (horizontalState ell h σ b Z τ B C n).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [horizontalState, ih, horizontalDifference_mul]
    apply Prod.ext <;> simp only [horizontalState] <;> ring

theorem horizontalIncrementSum_mul (ell N : ℕ) (h σ b Z τ : ℝ) (a B C : ℂ) :
    horizontalIncrementSum ell h σ b Z τ (a * B) (a * C) N =
      Complex.normSq a * horizontalIncrementSum ell h σ b Z τ B C N := by
  simp only [horizontalIncrementSum, horizontalState_mul, horizontalDifference_mul,
    Complex.normSq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem horizontalFormAt_mul (ell : ℕ) (τ σ b Z : ℝ) (a B C : ℂ) :
    horizontalFormAt ell (τ, σ, b, Z, a * B, a * C) =
      Complex.normSq a * horizontalFormAt ell (τ, σ, b, Z, B, C) := by
  simp only [horizontalFormAt, horizontalIncrementSum_mul, Complex.normSq_mul]
  ring

/-- Homogeneity extends the compact unit-sphere estimate to every nonzero jet. -/
theorem horizontalForm_positive_of_unit_sphere (ell : ℕ) (τ σ b Z : ℝ)
    (hunit : ∀ B C : ℂ, (B, C) ∈ sphere (0 : ℂ × ℂ) 1 →
      0 < horizontalFormAt ell (τ, σ, b, Z, B, C))
    (B C : ℂ) (hBC : B ≠ 0 ∨ C ≠ 0) :
    0 < horizontalFormAt ell (τ, σ, b, Z, B, C) := by
  have hpair : (B, C) ≠ (0 : ℂ × ℂ) := by
    intro h
    have hB := congrArg Prod.fst h
    have hC := congrArg Prod.snd h
    exact hBC.elim (fun hn => hn hB) (fun hn => hn hC)
  have hn : 0 < ‖(B, C)‖ := norm_pos_iff.mpr hpair
  let a : ℝ := ‖(B, C)‖⁻¹
  have ha : 0 < a := inv_pos.mpr hn
  have hsphere : ((a : ℂ) * B, (a : ℂ) * C) ∈ sphere (0 : ℂ × ℂ) 1 := by
    change a • (B, C) ∈ sphere (0 : ℂ × ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact inv_mul_cancel₀ hn.ne'
  have hp := hunit ((a : ℂ) * B) ((a : ℂ) * C) hsphere
  rw [horizontalFormAt_mul] at hp
  exact pos_of_mul_pos_right hp (Complex.normSq_nonneg _)

end DefocusingNLS

end OAI
