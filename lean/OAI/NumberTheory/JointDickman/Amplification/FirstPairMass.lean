import OAI.NumberTheory.JointDickman.Amplification.FirstRepresentationSum
import OAI.NumberTheory.JointDickman.Amplification.EndpointConditionalMean

namespace OAI

/-! # The remaining mass of first coefficient pairs -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidateFirstPairMass (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
    if BlockCandidateAdmissible B L T H τ C ((i,t),ab) then
      candidateCoefficientFactor B L τ C χ ((i,t),ab)*
      (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
      (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ)) else 0

/-- Domination of one first pair after its remainder laws are normalized. -/
theorem candidateFirstPairMass_term_le {B L T H M : ℕ} {τ C : ℝ}
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (A D : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (he : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))) (hχ : χ ((i,t),(A,D)) ≤ 1) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D))*
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)) ≤
    (B : ℝ)*independentRootMean B L τ C*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ D, p) := by
  let e : BlockCandidateIndex M := ((i,t),(A,D))
  let QA := remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)
  let QD := remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)
  have hQA : 0 ≤ QA := div_nonneg (remainderTiltNormalizer_nonneg B A) (Nat.cast_nonneg _)
  have hQD : 0 ≤ QD := div_nonneg (remainderTiltNormalizer_nonneg B D) (Nat.cast_nonneg _)
  have hroot : 0 ≤ independentRootMean B L τ C/(B : ℝ) :=
    div_nonneg (independentRootMean_nonneg _ _ _ _) (Nat.cast_nonneg B)
  obtain ⟨_,_,_,hc,hrel,_,_,_,_,_,hclo,hchi,hblo,hbhi,_,hahi⟩ := he
  have htest := (regularCoefficientWeight_le B L τ C (candidateQuotient e)).trans
    (supportedEndpointTest_ge hB hT hTs hc hclo hchi hblo hbhi hrel hahi)
  let W := independentRootMean B L τ C/(B : ℝ)*
    (regularCoefficientWeight B L τ C (∏ p ∈ A, p)*QA)*
    (regularCoefficientWeight B L τ C (∏ p ∈ D, p)*QD)
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg hroot
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQA))
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQD)
  have hbase : W ≤ independentRootMean B L τ C/(B : ℝ)*
      (coefficientWeight B (∏ p ∈ A, p)*QA)*(coefficientWeight B (∏ p ∈ D, p)*QD) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (regularCoefficientWeight_le _ _ _ _ _) hQA) hroot)
      (mul_le_mul_of_nonneg_right (regularCoefficientWeight_le _ _ _ _ _) hQD)
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQD)
      (mul_nonneg hroot (mul_nonneg (coefficientWeight_nonneg _ _) hQA))
  calc
    _ = W*regularCoefficientWeight B L τ C (candidateQuotient e)*χ e := by
      dsimp only [W,QA,QD,e,candidateCoefficientFactor,candidateLow,candidateHigh]
      ring
    _ ≤ W*regularCoefficientWeight B L τ C (candidateQuotient e) :=
      mul_le_of_le_one_right (mul_nonneg hW (regularCoefficientWeight_nonneg _ _ _ _ _)) hχ
    _ ≤ (independentRootMean B L τ C/(B : ℝ)*
          (coefficientWeight B (∏ p ∈ A, p)*QA)*(coefficientWeight B (∏ p ∈ D, p)*QD))*
        supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ D, p) := by
      exact mul_le_mul hbase htest (regularCoefficientWeight_nonneg _ _ _ _ _)
        (mul_nonneg (mul_nonneg hroot (mul_nonneg (coefficientWeight_nonneg _ _) hQA))
          (mul_nonneg (coefficientWeight_nonneg _ _) hQD))
    _ = _ := by
      dsimp only [QA,QD]
      rw [coefficient_tilt_mass (by omega) hA,coefficient_tilt_mass (by omega) hD]
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
      field_simp

end JointDickman

end OAI
