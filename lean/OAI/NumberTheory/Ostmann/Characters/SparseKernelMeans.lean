import OAI.NumberTheory.Ostmann.Characters.SparseKernelEnergy

namespace OAI

/-! # Exact nonzero-residue sums for the sparse additive kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_eq_mul_additiveFourier_zero {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x, f x) = (p : ℂ) * additiveFourier f 0 := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [additiveFourier_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem sparseAdditiveKernel_zero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) :
    sparseAdditiveKernel E t 0 = (t : ℂ) * E.card / p := by
  rw [sparseAdditiveKernel_formula]
  simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

theorem sparseAdditiveKernel_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x) = 0 := by
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_fourier,
    ite_eq_right hE, mul_zero, mul_zero]

theorem sparseAdditiveKernel_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x) = -(t : ℂ) * E.card / p := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_sum E hE,
    sparseAdditiveKernel_zero]
  ring

theorem sparseAdditiveKernel_square_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * E.card / p := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : E.filter (fun b => (0 : ZMod p) - b ∈ E) = E := by
    ext b
    simp only [Finset.mem_filter, zero_sub, hE b, and_self]
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_square_fourier, he]
  field_simp

theorem sparseAdditiveKernel_square_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * ((E.card : ℂ) / p - ((E.card : ℂ) / p) ^ 2) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_square_sum E hE,
    sparseAdditiveKernel_zero]
  ring

end Ostmann

end OAI
