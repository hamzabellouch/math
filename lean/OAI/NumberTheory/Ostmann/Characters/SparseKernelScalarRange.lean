import OAI.NumberTheory.Ostmann.Characters.SparseKernelScalar

namespace OAI

/-! # Real scalar range of the sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem residueKernelScalar_sparse_real {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) :
    (residueKernelScalar S (sparseAdditiveKernel E t)).im = 0 := by
  rw [residueKernelScalar_sparse S E hS hSp hE]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem residueKernelScalar_sparse_lower {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) (ht : 0 ≤ t) :
    -t / p ≤ (residueKernelScalar S (sparseAdditiveKernel E t)).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hen : (∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ p := by
    simpa only [normalizedResidueIndicator_energy S hS hSp] using
      finiteSpectralProjection_energy_le E (normalizedResidueIndicator S)
  have he : residueKernelScalar S (sparseAdditiveKernel E t) =
      ((-t / (p : ℝ) ^ 2 *
        ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [residueKernelScalar_sparse S E hS hSp hE]
    push_cast
    rfl
  rw [he, Complex.ofReal_re]
  calc
    _ = -t / (p : ℝ) ^ 2 * p := by field_simp
    _ ≤ _ := mul_le_mul_of_nonpos_left hen (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))

end Ostmann

end OAI
