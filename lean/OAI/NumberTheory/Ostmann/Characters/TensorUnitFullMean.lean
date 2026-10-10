import OAI.NumberTheory.Ostmann.Characters.TensorUnitPolynomial
import OAI.NumberTheory.Ostmann.Characters.SparseUnitMassBounds

namespace OAI

/-! # Exact full unit mean and the truncated unit mass -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitMean_full_square {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i) :
    tensorUnitMean p (fun x => ∏ i, (1 + localSparseKernel (E i) (x i)) ^ 2) =
      ((∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i) : ℝ) : ℂ) := by
  rw [tensorUnitMean_product p (fun i x => (1 + localSparseKernel (E i) x) ^ 2)]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  exact (sparseKernelUnitFactor_mean (E i) (hE i) (hsym i) (Fact.out : (p i).Prime).one_lt).symm

theorem tensorUnitMean_truncated_close {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (K : ℕ) :
    ‖tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2) -
      ((∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i) : ℝ) : ℂ)‖ ≤
        2 * Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
          (1 - 100 / 103) ^ 2 := by
  rw [norm_sub_rev]
  rw [← tensorUnitMean_full_square p E hE hsym]
  exact tensorUnitMean_truncation_error p E hE hsym ε hε hε1 hc K

end Ostmann

end OAI
