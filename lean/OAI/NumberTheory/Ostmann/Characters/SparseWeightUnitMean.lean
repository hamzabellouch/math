import OAI.NumberTheory.Ostmann.Supply.NonnegativeSparseWeight
import OAI.NumberTheory.Ostmann.Characters.TensorUnitFullMean
import OAI.NumberTheory.Ostmann.Characters.SparseTruncationRate

namespace OAI

/-! # The exact real unit mean of the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorRealUnitMean {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℝ) : ℝ :=
  (∏ i, ((p i : ℝ) - 1)⁻¹) *
    ∑ x : (∀ i, NonzeroResidue (p i)), f (fun i => x i)

theorem tensorUnitMean_ofReal {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℝ) :
    tensorUnitMean p (fun x => (f x : ℂ)) = (tensorRealUnitMean p f : ℂ) := by
  unfold tensorUnitMean tensorRealUnitMean
  push_cast
  rfl

theorem sparseWeightUnitMean_close {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    |tensorRealUnitMean p (sparseSubsetWeight p S K) - U| ≤ Real.exp (-5 * L) := by
  intro U
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  have hs (i : Fin n) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have he := tensorUnitMean_truncated_close p E (fun i => (hs i).1)
    (fun i => (hs i).2.1) ε hε (by linarith) (fun i => (hs i).2.2.1) K
  have hf : (fun x => elementaryTruncation (fun i => localSparseKernel (E i) (x i)) K ^ 2) =
      (fun x => (sparseSubsetWeight p S K x : ℂ)) := by
    funext x
    exact (sparseSubsetWeight_complex p S K x).symm
  rw [hf, tensorUnitMean_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he.trans (sparse_truncation_error_rate L _ K hL hH hK)

end Ostmann

end OAI
