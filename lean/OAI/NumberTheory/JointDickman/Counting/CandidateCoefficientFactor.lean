import OAI.NumberTheory.JointDickman.Amplification.RegularPairChangeOfMeasure

namespace OAI

/-! # Separating the deterministic and remainder factors of a candidate -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCoefficientFactor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) : ℝ :=
  (regularCoefficientWeight B L τ C (candidateLow e)*
    regularCoefficientWeight B L τ C (candidateHigh e)*
    regularCoefficientWeight B L τ C (candidateQuotient e))/(B : ℝ)*χ e*
      independentRootMean B L τ C

theorem candidateCoefficientFactor_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) (hχ : 0 ≤ χ e) :
    0 ≤ candidateCoefficientFactor B L τ C χ e := by
  unfold candidateCoefficientFactor
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
      (regularCoefficientWeight_nonneg _ _ _ _ _))
    (regularCoefficientWeight_nonneg _ _ _ _ _)) (Nat.cast_nonneg B)) hχ)
    (independentRootMean_nonneg _ _ _ _)

theorem candidateMeanWeight_factor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      candidateCoefficientFactor B L τ C χ e*
        regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
        regularResidueWeight B L τ C (S e.1.2 \ e.2.2) := by
  rw [candidateMeanWeight_eq]
  unfold candidateCoefficientFactor
  ring

theorem candidateCoefficientFactor_zero_left {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C A) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  unfold candidateCoefficientFactor candidateLow
  rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hA,ite_eq_right hr]
  simp

theorem candidateCoefficientFactor_zero_right {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hD : D ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C D) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  have hz : regularCoefficientWeight B L τ C (candidateHigh ((i,t),(A,D))) = 0 := by
    change regularCoefficientWeight B L τ C (∏ p ∈ D, p) = 0
    rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hD,ite_eq_right hr]
  simp only [candidateCoefficientFactor,hz,mul_zero,zero_div,zero_mul]


/-- The local site kernel is a sum of deterministic factors times the two
regular remainder weights. -/
theorem candidateSiteKernel_factor_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R,
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
          regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2) := by
  unfold candidateSiteKernel
  rw [latentCandidateKernel_representation_sum B L T H M τ C _ χ i t hit]
  have hne : i ≠ t := ne_of_lt hit
  simp only [Function.update_of_ne hne,Function.update_self]
  apply sum_congr rfl
  intro ab _
  rw [candidateMeanWeight_factor]
  simp only [Function.update_of_ne hne,Function.update_self]

end JointDickman

end OAI
