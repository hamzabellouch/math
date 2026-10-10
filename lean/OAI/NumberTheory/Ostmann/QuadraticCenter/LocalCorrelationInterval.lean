import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationIntervalPhase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem residue_grid_linear_sum_bound {q : ℕ} [NeZero q] (α : ℝ) (a : ℤ) (N : ℕ) :
    (∑ h : ZMod q,
      ‖∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q))‖) ≤
        2 * N + 2 * q * (harmonic q : ℝ) := by
  apply separated_linear_sum_bound Finset.univ
    (fun h : ZMod q => α + h.val / q)
    (fun h : ZMod q =>
      ‖∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q))‖)
    (Nat.pos_of_neZero q) (Nat.cast_nonneg N)
  · intro i _ j _ hij m
    exact shifted_residue_grid_spacing α i j hij m
  · intro h _
    positivity
  · intro h _
    rw [shifted_linear_sum_norm]
    exact (linear_weyl_bound _ N).1
  · intro h _
    rw [shifted_linear_sum_norm]
    exact (linear_weyl_bound _ N).2

theorem interval_fourier_expansion {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) (α : ℝ) (a : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, F ((a + (n : ℤ) : ℤ) : ZMod q) *
      weylPhase (((a : ℝ) + n) * α)) =
      ∑ h : ZMod q, normalizedCoefficient F h *
        ∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q)) := by
  have hp (h : ZMod q) (n : ℕ) :
      ZMod.stdAddChar (((a + (n : ℤ) : ℤ) : ZMod q) * h) *
          weylPhase (((a : ℝ) + n) * α) =
        weylPhase (((a : ℝ) + n) * (α + h.val / q)) := by
    rw [stdAddChar_integer_mul_eq_weyl, ← weylPhase_add]
    congr 1
    push_cast
    ring
  simp_rw [normalizedCoefficient_inversion F]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, hp]

theorem periodic_interval_twist_bound {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, F ((a + (n : ℤ) : ℤ) : ZMod q) *
      weylPhase (((a : ℝ) + n) * α)‖ ≤ A * (2 * N + 2 * q * (harmonic q : ℝ)) := by
  rw [interval_fourier_expansion]
  calc
    _ ≤ ∑ h : ZMod q, ‖normalizedCoefficient F h *
        ∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h : ZMod q, A *
        ‖∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q))‖ := by
      apply Finset.sum_le_sum
      intro h _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcoeff h) (norm_nonneg _)
    _ = A * (∑ h : ZMod q,
        ‖∑ n ∈ Finset.range N, weylPhase (((a : ℝ) + n) * (α + h.val / q))‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (residue_grid_linear_sum_bound α a N) hA

end Ostmann.QuadraticCenter

end

end OAI
