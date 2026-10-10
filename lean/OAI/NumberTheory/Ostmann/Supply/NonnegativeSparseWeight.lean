import OAI.NumberTheory.Ostmann.Characters.SparseTruncatedWeight

namespace OAI

/-! # The real nonnegative weight represented by the truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem elementaryTruncation_conj {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, conj (b i) = b i) (K : ℕ) :
    conj (elementaryTruncation b K) = elementaryTruncation b K := by
  simp only [elementaryTruncation, map_sum, map_prod, hb]

theorem localSparseKernel_spectrum_real {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (x : ZMod p) :
    (localSparseKernel (largeTransformSpectrum (normalizedResidueTransform S)) x).im = 0 := by
  exact sparseAdditiveKernel_real _
    (largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S)) (17 / 20) x

noncomputable def sparseSubsetWeight {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) : ℝ :=
  ‖elementaryTruncation (fun i => localSparseKernel
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)) K‖ ^ 2

theorem sparseSubsetWeight_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    0 ≤ sparseSubsetWeight p S K x := sq_nonneg _

theorem sparseSubsetWeight_complex {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    (sparseSubsetWeight p S K x : ℂ) =
      elementaryTruncation (fun i => localSparseKernel
        (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)) K ^ 2 := by
  let b := fun i => localSparseKernel (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)
  have hb (i) : conj (b i) = b i := by
    have hi : (b i).im = 0 := localSparseKernel_spectrum_real (S i) (x i)
    apply Complex.ext <;> simp [hi]
  have he := elementaryTruncation_conj b hb K
  have hh := Complex.mul_conj' (elementaryTruncation b K)
  rw [he, ← pow_two] at hh
  simpa only [sparseSubsetWeight, Complex.ofReal_pow, b] using hh.symm

theorem sparseSubsetWeight_point_pairing {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (truncatedSparseTensorKernel p S K) =
        (sparseSubsetWeight p S K (fun i => a i - b i) : ℂ) := by
  rw [sparseSubsetWeight_complex]
  exact truncatedSparseTensorKernel_point_pairing p S a b ha hb K

end Ostmann

end OAI
