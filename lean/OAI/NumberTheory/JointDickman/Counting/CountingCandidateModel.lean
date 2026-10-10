import OAI.NumberTheory.JointDickman.Counting.CountingArithmeticFeatures
import OAI.NumberTheory.JointDickman.Amplification.RampedCandidateMean
import OAI.NumberTheory.JointDickman.Arithmetic.SubsetPrimeModel

namespace OAI

/-! # The finite prime-feature model for each ramped candidate entry -/
namespace JointDickman
open Finset

theorem subsetKernelBilinear_const_mul (B : ℕ) (g h : Finset ℕ → ℝ)
    (K : Finset ℕ → Finset ℕ → ℝ) (c : ℝ) :
    subsetKernelBilinear B g h (fun S R => c*K S R) = c*subsetKernelBilinear B g h K := by
  unfold subsetKernelBilinear
  simp only [mul_sum]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  ring

noncomputable def countingCandidateModel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ)
    (S R : Finset ℕ) : ℝ :=
  (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*
    subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c H T σ y x) S R

theorem countingCandidateModel_mean (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h) (countingCandidateModel P m B L j τ C c H T σ) =
    independentRootMean B L τ C*((singularSeries j/(j : ℝ))*(∑ x, ∑ y,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*h x*g y*
        countingPrimeKernel P m B j c H T σ x y)) := by
  unfold countingCandidateModel
  rw [subsetKernelBilinear_const_mul,subsetKernelBilinear_primeModel]
  rw [sum_comm]
  simp only [mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

theorem countingCandidateModel_bound (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ K : ℝ)
    (hseries : 0 ≤ singularSeries j)
    (hK : ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ K)
    (S R : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c H T σ S R| ≤
      (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*K := by
  unfold countingCandidateModel subsetPrimeModel
  rw [abs_mul,abs_of_nonneg (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))]
  exact mul_le_mul_of_nonneg_left (hK _ _) (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))

end JointDickman

end OAI
