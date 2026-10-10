import OAI.NumberTheory.Ostmann.Characters.SparseKernelEnergy
import OAI.NumberTheory.Ostmann.Supply.ResidueProjectionScalar

namespace OAI

/-! # The scalar decrease contributed by the sparse local kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residueKernelScalar {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (k : ZMod p → ℂ) : ℂ :=
  ∑ x, conj (uniformResidueVector S x) *
    rawAdditiveKernelAction k (uniformResidueVector (Finset.univ \ S)) x

theorem residueKernelScalar_sparse {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t : ℝ) :
    residueKernelScalar S (sparseAdditiveKernel E t) =
      -(t : ℂ) / (p : ℂ) ^ 2 *
        ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ) := by
  unfold residueKernelScalar rawAdditiveKernelAction
  simp_rw [sparseAdditiveKernel_action]
  calc
    _ = (t : ℂ) * (∑ x, conj (uniformResidueVector S x) *
        finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S)) x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [residueProjection_scalar S E hS hSp hE]; ring

theorem residueKernelScalar_sparse_re_le {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (t ε : ℝ) (ht : 0 ≤ t)
    (henergy : (1 - ε ^ 2) * p ≤
      ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) :
    (residueKernelScalar S (sparseAdditiveKernel E t)).re ≤ -(t * (1 - ε ^ 2)) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [residueKernelScalar_sparse S E hS hSp hE]
  have hre : (-(t : ℂ) / (p : ℂ) ^ 2 *
      ((∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 : ℝ) : ℂ)).re =
      -t / (p : ℝ) ^ 2 * ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
      ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  calc
    _ ≤ -t / (p : ℝ) ^ 2 * ((1 - ε ^ 2) * p) :=
      mul_le_mul_of_nonpos_left henergy (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
    _ = _ := by field_simp

end Ostmann

end OAI
