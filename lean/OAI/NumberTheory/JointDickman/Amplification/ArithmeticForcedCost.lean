import OAI.NumberTheory.JointDickman.Amplification.ArithmeticPatternMeans
import OAI.NumberTheory.JointDickman.Amplification.CandidateForcedProbability
import OAI.NumberTheory.JointDickman.Amplification.ActualCandidateProduct

namespace OAI

/-! # Weighted cost of forced third-site hits in the arithmetic block -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem blockPatternEquiv_symm_sites {B M : ℕ}
    (S : Fin M → (auxiliaryPrimes B).powerset) :
    primePatternsSites ((blockPatternEquiv B M).symm S) = (fun i => (S i).val) := by
  have h := (blockPatternEquiv B M).apply_symm_apply S
  funext i
  exact congrArg Subtype.val (congrFun h i)

theorem arithmetic_forced_cost {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      arithmeticSquareMean B (fun u => (B : ℝ)^10 *
        (if ForcedCandidateHit B L T H M τ C
          (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)) ≤
      (B : ℝ)^10 * (5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ) := by
  filter_upwards [forcedCandidateHit_probability hL hτ hτsmall,eventually_ge_atTop 2]
    with B hprob hB
  intro C T H M hT hMexp hM
  let F := fun S : BlockPrimePatterns B M => (B : ℝ)^10 *
    (if ForcedCandidateHit B L T H M τ C (primePatternsSites S) then (1 : ℝ) else 0)
  have hcap S : |F S| ≤ 1*(B : ℝ)^10 := by
    dsimp only [F]
    split_ifs <;> simp [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) B) 10)]
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).1
  have hc := arithmeticSquareMean_pattern_comparison (by omega : 1 < B) hM hsize F
    (C := 1) (by norm_num) hcap
  have hleft : arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u)) =
      arithmeticSquareMean B (fun u => (B : ℝ)^10 *
        (if ForcedCandidateHit B L T H M τ C
          (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)) := by
    apply congrArg (arithmeticSquareMean B)
    funext u
    have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
        (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
      funext (primePatternsSites_arithmetic B M u)
    dsimp only [F]
    rw [hs]
  have hright : finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => F ((blockPatternEquiv B M).symm S)) =
      (B : ℝ)^10 * finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ForcedCandidateHit B L T H M τ C (fun i => (S i).val)) := by
    simp only [F,blockPatternEquiv_symm_sites,finiteProbability_eq_indicator_mean,
      finiteExpectation_const_mul]
  rw [hleft,hright] at hc
  have hp := mul_le_mul_of_nonneg_left (hprob C T H M hT hMexp)
    (pow_nonneg (Nat.cast_nonneg (α := ℝ) B) 10)
  have hu := (le_abs_self _).trans hc
  simp only [mul_one] at hu
  linarith only [hp,hu]

end JointDickman

end OAI
