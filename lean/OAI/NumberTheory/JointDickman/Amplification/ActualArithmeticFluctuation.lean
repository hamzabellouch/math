import OAI.NumberTheory.JointDickman.Amplification.ArithmeticForcedCost
import OAI.NumberTheory.JointDickman.Amplification.MaskedArithmeticFluctuation

namespace OAI

/-! # Removing the root-identification exceptions from the arithmetic kernel -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

noncomputable def actualCandidateCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) : ℝ :=
  kernelCutNorm (fun i k => actualCandidateKernel B L T H M τ C χ u i k-
    latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ i k)

theorem actualCandidateCutError_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hf : ¬ ForcedCandidateHit B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (ha : ¬ ActualCoefficientException B L T H M τ C u)
    (hm : ¬ MaskedCoefficientException B L T H M τ C u) :
    actualCandidateCutError B L T H M τ C χ u =
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u) := by
  have hk := actualCandidateKernel_eq_masked hT χ
    (fun e he hw => hf ⟨e,he,hw⟩) ha hm
  unfold actualCandidateCutError
  rw [hk]
  unfold maskedDigitCutError patternRootCutError
  rw [residuePrimePatterns_arithmetic]
  have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
      (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
    funext (primePatternsSites_arithmetic B M u)
  rw [hs]
  have hd : arithmeticFirstDigits B u = (fun p : auxiliaryPrimes B => (u : ZMod p.val)) := by
    funext p
    let : NeZero p.val := ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
    exact primeDigits_first u
  rw [hd]

theorem actualCandidateCutError_pointwise {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hcap : actualCandidateCutError B L T H M τ C χ u ≤ (B : ℝ)^10) :
    actualCandidateCutError B L T H M τ C χ u ≤
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u)+
        (B : ℝ)^10 *
          ((if ForcedCandidateHit B L T H M τ C
            (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)+
           (if ActualCoefficientException B L T H M τ C u then 1 else 0)+
           (if MaskedCoefficientException B L T H M τ C u then 1 else 0)) := by
  have hg : 0 ≤ maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u) :=
    kernelCutNorm_nonneg _
  have hQ : 0 ≤ (B : ℝ)^10 := pow_nonneg (Nat.cast_nonneg B) _
  by_cases hf : ForcedCandidateHit B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))
  · simp only [hf,ite_true]
    split_ifs <;> nlinarith
  · by_cases ha : ActualCoefficientException B L T H M τ C u
    · simp only [hf,ha,ite_false,ite_true]
      split_ifs <;> nlinarith
    · by_cases hm : MaskedCoefficientException B L T H M τ C u
      · simp only [hf,ha,hm,ite_false,ite_true]
        nlinarith
      · rw [actualCandidateCutError_eq_masked hT χ hf ha hm]
        simp only [hf,ha,hm,ite_false,mul_zero,add_zero,le_refl]

end JointDickman

end OAI
