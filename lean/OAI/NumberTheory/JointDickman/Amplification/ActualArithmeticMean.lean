import OAI.NumberTheory.JointDickman.Amplification.ActualArithmeticFluctuation
import OAI.NumberTheory.JointDickman.Counting.CoefficientErrorScale

namespace OAI

/-! # Vanishing arithmetic candidate fluctuations after all root exceptions -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem actual_arithmetic_fluctuation_bound
    (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
      0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤
        K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+
        coefficientRootError B+
        (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+4/(B : ℝ) := by
  obtain ⟨K,hK,hmask⟩ := masked_arithmetic_fluctuation_bound hFord hMertens hL hτ hτsmall
  refine ⟨K,hK,?_⟩
  filter_upwards [hmask,arithmetic_forced_cost hL hτ hτsmall,
    candidate_root_error_cap hL hτ hτsmall,blockCandidates_card hL hτ hτsmall,
    eventually_ge_atTop 2] with B hmask hforced hcap hcount hB
  intro C T H M hT hTs hTP hM0 hM hMexp χ hχ
  have hTe : (T : ℝ) ≤ Real.exp B := hTs.trans (Real.exp_le_exp.mpr (by
    have hBr := Nat.cast_nonneg (α := ℝ) B
    nlinarith))
  have hP : 0 < auxiliaryCutoff B := pow_pos (by omega) _
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).1
  have hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).2
  have hN : M^2*B^2 ≤ B^6 := by
    calc
      _ ≤ (B^2)^2*B^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
      _ = _ := by ring
  let fa := fun u => if ActualCoefficientException B L T H M τ C u then (1 : ℝ) else 0
  let fm := fun u => if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0
  let ff := fun u => if ForcedCandidateHit B L T H M τ C
    (fun i => coefficientPrimeSet B (u+(i.val+1))) then (1 : ℝ) else 0
  have ha := actual_coefficient_exception_bound hB hTe hMexp hP hTP
    (fun S => hcount C T H M S)
  have hm := masked_coefficient_exception_bound hB hTe hMexp hP hsize hhalf
    (fun S => hcount C T H M S)
  have hcoeff : (B : ℝ)^10*(arithmeticSquareMean B fa+arithmeticSquareMean B fm) ≤
      coefficientRootError B := coefficient_error_polynomial hB hN ha hm
  have hpoint u : actualCandidateCutError B L T H M τ C χ u ≤
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u)+
        (B : ℝ)^10*(ff u+fa u+fm u) := by
    apply actualCandidateCutError_pointwise hTP χ
    have hc : |actualCandidateCutError B L T H M τ C χ u| ≤ (B : ℝ)^10 :=
      hcap C T H M hM0 hM (fun i => coefficientPrimeSet B (u+(i.val+1))) χ hχ
        (primeSiteTranspose _ (auxiliaryPrimes B)
          (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u)))
    exact (le_abs_self _).trans hc
  have he := arithmeticSquareMean_mono B hpoint
  rw [arithmeticSquareMean_add,arithmeticSquareMean_const_mul,
    arithmeticSquareMean_add,arithmeticSquareMean_add] at he
  have hfo := hforced C T H M hTe hMexp hM
  rw [arithmeticSquareMean_const_mul] at hfo
  have hma := hmask C T H M hT hTs hM0 hM hMexp χ hχ
  change (B : ℝ)^10*arithmeticSquareMean B ff ≤
    (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ) at hfo
  calc
    _ ≤ arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u))+
        (B : ℝ)^10*arithmeticSquareMean B ff+
        (B : ℝ)^10*(arithmeticSquareMean B fa+arithmeticSquareMean B fm) := he.trans_eq (by ring)
    _ ≤ (K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+2/(B : ℝ))+
        ((B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ))+
        coefficientRootError B := add_le_add (add_le_add hma hfo) hcoeff
    _ = _ := by ring

end JointDickman

end OAI
