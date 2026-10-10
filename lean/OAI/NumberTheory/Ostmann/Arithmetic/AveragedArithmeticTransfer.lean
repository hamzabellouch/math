import OAI.NumberTheory.Ostmann.Characters.PivotArithmeticTransfer

namespace OAI

/-! # Retaining the complex off-diagonal through the outside average -/

namespace Ostmann

open scoped BigOperators

/-- The real-part form must be averaged before taking the norm of the next
amplitude. The original outside law may be a subprobability law. -/
theorem averaged_arithmetic_transfer {Y : Type*} [Fintype Y]
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (η θ : Y → ℂ) (D : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ y, ‖η y‖ ^ 2 ≤ C * (D y + (θ y).re)) :
    ‖∑ y, (μ y : ℂ) * η y‖ ^ 2 ≤
      C * ((∑ y, μ y * D y) + ‖∑ y, (μ y : ℂ) * θ y‖) := by
  have hRe : (∑ y, (μ y : ℂ) * θ y).re = ∑ y, μ y * (θ y).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  calc
    _ ≤ ∑ y, μ y * ‖η y‖ ^ 2 := subprobability_weighted_norm_sq_le μ hμ hmass η
    _ ≤ ∑ y, μ y * (C * (D y + (θ y).re)) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hlocal y) (hμ y)
    _ = ∑ y, C * (μ y * D y + μ y * (θ y).re) := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = C * ((∑ y, μ y * D y) + ∑ y, μ y * (θ y).re) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = C * ((∑ y, μ y * D y) + (∑ y, (μ y : ℂ) * θ y).re) := by rw [hRe]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (Complex.re_le_norm _)) hC

/-- A concrete harmonic-prior loss bounded by exp(d) gives the normalized
transfer inequality used by the iteration theorem. -/
theorem normalized_arithmetic_transfer (η θ : ℂ) (D C d : ℝ)
    (hD : 0 ≤ D) (hC : C ≤ Real.exp d)
    (htransfer : ‖η‖ ^ 2 ≤ C * (D + ‖θ‖)) :
    Real.exp (-d) * ‖η‖ ^ 2 ≤ D + ‖θ‖ := by
  have hCD : Real.exp (-d) * C ≤ 1 := by
    calc
      _ ≤ Real.exp (-d) * Real.exp d := mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ Real.exp (-d) * (C * (D + ‖θ‖)) :=
      mul_le_mul_of_nonneg_left htransfer (Real.exp_pos _).le
    _ = (Real.exp (-d) * C) * (D + ‖θ‖) := by ring
    _ ≤ 1 * (D + ‖θ‖) := mul_le_mul_of_nonneg_right hCD (add_nonneg hD (norm_nonneg _))
    _ = _ := one_mul _

end Ostmann

end OAI
