import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy

namespace OAI

/-! # Grouping the transfer diagonal before expanding the square -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedCoefficient {A K : Type*} [Fintype A]
    (key : A → K) (z : A → ℂ) (k : K) : ℂ :=
  ∑ a, if key a = k then z a else 0

/-- The key comprises the inherited product and its frequency. Ordered
arrangements with that key are summed inside the square. -/
theorem diagonal_grouped_identity {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℂ) :
    (∑ a : A, ∑ b : A, if key a = key b then w (key a) * z a * star (z b) else 0) =
      ∑ k : K, w k * groupedCoefficient key z k * star (groupedCoefficient key z k) := by
  rw [Finset.sum_comm]
  symm
  unfold groupedCoefficient
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, apply_ite, star_zero,
    ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key b = key a <;> simp [h]

theorem diagonal_real_eq_sum_sq {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) :
    (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re =
      ∑ k : K, w k * ‖groupedCoefficient key z k‖ ^ 2 := by
  rw [diagonal_grouped_identity key z (fun k => (w k : ℂ))]
  simp only [mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

theorem diagonal_real_nonneg {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re := by
  rw [diagonal_real_eq_sum_sq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)

end Ostmann

end OAI
