import OAI.NumberTheory.Ostmann.Supply.AveragedKernelPairing

namespace OAI

/-! # The sparse weight average over two actual finite summand sets -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseWeightPairAverage {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i)) : ℝ :=
  (A.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ * ∑ x ∈ A, ∑ y ∈ B,
    sparseSubsetWeight p S K (fun i => a x i - b y i)

theorem sparseWeightPairAverage_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i)) :
    0 ≤ sparseWeightPairAverage p S K A B a b := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
    (fun y _ => sparseSubsetWeight_nonneg p S K _))

theorem sparseWeightPairAverage_identity {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i) (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i) :
    kernelPairingLinearMap
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
      (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))
      (truncatedSparseTensorKernel p S K) =
        (sparseWeightPairAverage p S K A B a b : ℂ) := by
  rw [kernelPairing_averages]
  unfold sparseWeightPairAverage
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact sparseSubsetWeight_point_pairing p S K (a x) (b y) (ha x hx) (hb y hy)

theorem sparseWeightPairAverage_le {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) {ι κ : Type*}
    (A : Finset ι) (B : Finset κ) (a : ι → ∀ i, ZMod (p i)) (b : κ → ∀ i, ZMod (p i))
    (ha : ∀ x ∈ A, ∀ i, a x i ∈ S i) (hb : ∀ y ∈ B, ∀ i, b y i ∈ Finset.univ \ S i) :
    sparseWeightPairAverage p S K A B a b ≤
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ *
        countingVectorNorm (lowModeVector (2 * K)
          (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) *
        countingVectorNorm (lowModeVector (2 * K)
          (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))) := by
  have he := sparseWeightPairAverage_identity p S K A B a b ha hb
  have hh := truncatedSparseTensorKernel_pairing_le p S K
    (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
    (averagedCoordinates B (fun y => tensorPointCoordinates p (fun i => Finset.univ \ S i) (b y)))
  change ‖kernelPairingLinearMap _ _ _‖ ≤ _ at hh
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sparseWeightPairAverage_nonneg p S K A B a b)] at hh
  exact hh

end Ostmann

end OAI
