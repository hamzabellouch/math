import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitAverages

namespace OAI

/-! # Coefficient exceptions for the actual arithmetic candidate family -/

namespace JointDickman
open Finset PublishedInputs Classical

noncomputable def arithmeticSquareMean (B : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ u ∈ range (∏ p ∈ auxiliaryPrimes B, p^2), f u)/
    (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2)

noncomputable def residueCandidates (B L T H M : ℕ) (τ C : ℝ)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : Finset (BlockCandidateIndex M) :=
  blockCandidates B L T H M τ C (primePatternsSites (residuePrimePatterns r))

theorem residueCandidates_arithmetic (B L T H M u : ℕ) (τ C : ℝ) :
    residueCandidates B L T H M τ C (arithmeticFirstDigits B u) =
      blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) := by
  unfold residueCandidates
  rw [residuePrimePatterns_arithmetic]
  have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
      (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
    funext (primePatternsSites_arithmetic B M u)
  rw [hs]

def ActualCoefficientException (B L T H M : ℕ) (τ C : ℝ) (u : ℕ) : Prop :=
  ArithmeticCoefficientHit B
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (candidateArithmeticQuotient u)

def MaskedCoefficientException (B L T H M : ℕ) (τ C : ℝ) (u : ℕ) : Prop :=
  MaskedCoefficientEvent
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val))

theorem actual_coefficient_exception_bound {B L T H M N : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (hTP : T ≤ auxiliaryCutoff B)
    (hcard : ∀ S : Fin M → Finset ℕ, (blockCandidates B L T H M τ C S).card ≤ N) :
    arithmeticSquareMean B (fun u => if ActualCoefficientException B L T H M τ C u then 1 else 0) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  let I := residueCandidates B L T H M τ C
  let F := fun r t => if CoefficientDigitEvent B (I r) r t then (1 : ℝ) else 0
  have hpoint (u : ℕ) :
      (if ActualCoefficientException B L T H M τ C u then (1 : ℝ) else 0) ≤
        F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
    by_cases hu : ActualCoefficientException B L T H M τ C u
    · have hd := arithmetic_coefficient_hit_implies_digit _ (candidateArithmeticQuotient u)
        (fun _ he => (mem_blockCandidates.mp he).2)
        (fun _ he => candidateArithmeticQuotient_equation hTP he) hu
      have he : CoefficientDigitEvent B (I (arithmeticFirstDigits B u))
          (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
        simpa only [I,residueCandidates_arithmetic] using hd
      simp only [F,hu,he,ite_true,le_refl]
    · simp only [hu,ite_false,F]
      split_ifs <;> norm_num
  calc
    _ ≤ arithmeticSquareMean B (fun u => F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u)) := by
      apply div_le_div_of_nonneg_right (sum_le_sum (fun u _ => hpoint u))
      positivity
    _ = finiteExpectation (primeDigitMass B) (fun r => finiteProbability (primeDigitMass B)
        (CoefficientDigitEvent B (I r) r)) := by
      rw [arithmeticSquareMean,prime_square_crt_average]
      apply congrArg (finiteExpectation (primeDigitMass B))
      funext r
      exact (finiteProbability_eq_indicator_mean _ _).symm
    _ ≤ _ := adaptive_coefficient_digit_probability hB hT hM hP I
      (fun _ _ he => (mem_blockCandidates.mp he).2) (fun r => hcard _)

theorem masked_coefficient_exception_bound {B L T H M N : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (hcard : ∀ S : Fin M → Finset ℕ, (blockCandidates B L T H M τ C S).card ≤ N) :
    arithmeticSquareMean B (fun u => if MaskedCoefficientException B L T H M τ C u then 1 else 0) ≤
      24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  let I := fun S : BlockPrimePatterns B M => blockCandidates B L T H M τ C (primePatternsSites S)
  let F := fun r : ∀ p : auxiliaryPrimes B, ZMod p.val =>
    if MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r then (1 : ℝ) else 0
  have hF (u : ℕ) :
      (if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0) =
        F (arithmeticFirstDigits B u) := by
    have hd : arithmeticFirstDigits B u = (fun p : auxiliaryPrimes B => (u : ZMod p.val)) :=
      funext (fun (p : auxiliaryPrimes B) => primeDigits_first u)
    have hs := residueCandidates_arithmetic B L T H M u τ C
    change (if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0) =
      if MaskedCoefficientEvent (residueCandidates B L T H M τ C (arithmeticFirstDigits B u))
        (residuePrimePatterns (arithmeticFirstDigits B u)) (arithmeticFirstDigits B u) then 1 else 0
    rw [hs,residuePrimePatterns_arithmetic,hd]
    rfl
  calc
    _ = arithmeticSquareMean B (fun u => F (arithmeticFirstDigits B u)) :=
      congrArg (arithmeticSquareMean B) (funext hF)
    _ = finiteExpectation (primeDigitMass B) F := by
      rw [arithmeticSquareMean,prime_square_crt_average B (fun r _ => F r)]
      simp only [finiteExpectation_const _ (primeDigitMass_sum B)]
    _ = finiteProbability (primeDigitMass B) (fun r =>
        MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r) :=
      (finiteProbability_eq_indicator_mean _ _).symm
    _ ≤ _ := adaptive_masked_coefficient_probability hB hT hM hP hsize hhalf I
      (fun _ _ he => (mem_blockCandidates.mp he).2) (fun _ => hcard _)

end JointDickman

end OAI
