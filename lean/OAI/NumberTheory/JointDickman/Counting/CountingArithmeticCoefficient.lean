import OAI.NumberTheory.JointDickman.Counting.CountingPeriodicModel
import OAI.NumberTheory.JointDickman.Counting.CountingCoefficientRegularity
import OAI.NumberTheory.JointDickman.Amplification.CoarseCenteredWeight

namespace OAI

/-! # Exact arithmetic evaluation of the periodic finite-feature coefficient -/
namespace JointDickman
open Finset Classical

theorem coefficientPrimeSet_feature_input (B n : ℕ) :
    (fun p : auxiliaryPrimes B => decide (p.val ∈ coefficientPrimeSet B n)) =
      (fun p : auxiliaryPrimes B => decide (p.val ∣ n)) := by
  funext p
  simp only [coefficientPrimeSet,mem_filter,p.property,true_and]

theorem countingCandidateWithSeries_arithmetic (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) {n v : ℕ} (hn : n ≠ 0) (hv : v ≠ 0) :
    countingCandidateWithSeries F P m B L j τ C c D T σ
      (coefficientPrimeSet B n) (coefficientPrimeSet B v) =
    (independentRootMean B L τ C*(F j/(j : ℝ)))*
      ∑ d ∈ P.support, ∑ a, ∑ b, countingTermCoefficient P d (m d) B j (c d) (D d) T σ a b*
        primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B a) v*
        primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b) n := by
  unfold countingCandidateWithSeries subsetPrimeModel
  rw [coefficientPrimeSet_feature_input,coefficientPrimeSet_feature_input]
  dsimp only
  rw [countingPrimeKernel_coefficients]
  simp only [primeSiteWeight_apply _ _ hn,primeSiteWeight_apply _ _ hv]

end JointDickman

end OAI
