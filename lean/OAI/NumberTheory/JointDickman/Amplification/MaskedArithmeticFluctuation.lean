import OAI.NumberTheory.JointDickman.Counting.BlockPatternTranspose
import OAI.NumberTheory.JointDickman.Counting.ArithmeticCoefficientProbability
import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootFluctuation

namespace OAI

/-! # The masked arithmetic CRT kernel inherits the root fluctuation bound -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem siteConditionedRootProduct_nonneg {B M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (R : auxiliaryPrimes B → I.powerset) :
    0 ≤ siteConditionedRootProductMass B I S R := by
  apply finiteProductMass_nonneg
  intro p A
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  exact siteConditionedRootPrimeMass_nonneg I S p.val A

theorem siteConditionedRootProduct_sum {B M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) :
    (∑ R, siteConditionedRootProductMass B I S R) = 1 := by
  apply finiteProductMass_sum
  intro p
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  exact siteConditionedRootPrimeMass_sum I S p.val (hsize p.val p.property)

noncomputable def patternRootCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : BlockPrimePatterns B M)
    (R : auxiliaryPrimes B → (blockCandidates B L T H M τ C (primePatternsSites S)).powerset) : ℝ :=
  kernelCutNorm (fun i k => independentCandidateKernel B L T H M τ C (primePatternsSites S) χ
      (primeSiteTranspose _ (auxiliaryPrimes B) R) i k-
    latentCandidateKernel B L T H M τ C (primePatternsSites S) χ i k)

noncomputable def patternRootMean (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : BlockPrimePatterns B M) : ℝ :=
  finiteExpectation
    (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (primePatternsSites S))
      (primePatternsSites S)) (patternRootCutError B L T H M τ C χ S)

noncomputable def maskedDigitCutError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : ℝ :=
  patternRootCutError B L T H M τ C χ (residuePrimePatterns r)
    (maskedPrimeRootFamily (blockCandidates B L T H M τ C (primePatternsSites (residuePrimePatterns r)))
      (residuePrimePatterns r) r)

theorem patternRootMean_transpose (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) :
    (∑ S : BlockPrimePatterns B M, bernoulliProductMass univ
      (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S *
        patternRootMean B L T H M τ C χ S) =
      averagedConditionedRootError B L T H M τ C χ := by
  exact blockPatternEquiv_sum (fun S => finiteExpectation
    (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (fun i => (S i).val))
      (fun i => (S i).val))
    (fun R => kernelCutNorm (fun i k =>
      independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ
        (primeSiteTranspose _ (auxiliaryPrimes B) R) i k-
      latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)))

theorem patternRootMean_abs_bound {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hcap : ∀ S R, |patternRootCutError B L T H M τ C χ S R| ≤ (B : ℝ)^10)
    (S : BlockPrimePatterns B M) : |patternRootMean B L T H M τ C χ S| ≤ (B : ℝ)^10 := by
  let w := siteConditionedRootProductMass B (blockCandidates B L T H M τ C (primePatternsSites S))
    (primePatternsSites S)
  exact (finiteExpectation_abs_bound w _ (siteConditionedRootProduct_nonneg _ _)).trans
    ((finiteExpectation_mono w (siteConditionedRootProduct_nonneg _ _) (hcap S)).trans_eq
      (finiteExpectation_const w (siteConditionedRootProduct_sum _ _ hsize) _))

theorem maskedDigitCutError_mean {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (χ : BlockCandidateIndex M → ℝ) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) :
    finiteExpectation (primeDigitMass B) (maskedDigitCutError B L T H M τ C χ) =
      ∑ S : BlockPrimePatterns B M, categoricalProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S *
          patternRootMean B L T H M τ C χ S := by
  exact masked_residue_disintegration hsize
    (fun S => blockCandidates B L T H M τ C (primePatternsSites S))
    (patternRootCutError B L T H M τ C χ)

theorem maskedDigitCutError_comparison {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 1 < B) (hM : M ≤ B^2) (χ : BlockCandidateIndex M → ℝ)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hcap : ∀ S R, |patternRootCutError B L T H M τ C χ S R| ≤ (B : ℝ)^10) :
    |finiteExpectation (primeDigitMass B) (maskedDigitCutError B L T H M τ C χ)-
      averagedConditionedRootError B L T H M τ C χ| ≤ 2/(B : ℝ) := by
  have hc := block_sites_auxiliary_comparison hB hM
    (patternRootMean B L T H M τ C χ) (C := 1) (by norm_num)
    (fun S => by simpa only [one_mul] using patternRootMean_abs_bound χ hsize hcap S)
  rw [block_sites_crt_mean M (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hsize] at hc
  rw [← maskedDigitCutError_mean χ hsize,patternRootMean_transpose] at hc
  simpa only [mul_one] using hc

theorem masked_arithmetic_fluctuation_bound
    (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 →
      (M : ℝ) ≤ Real.exp B → ∀ χ : BlockCandidateIndex M → ℝ,
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ
        (arithmeticFirstDigits B u)) ≤
        K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+2/(B : ℝ) := by
  obtain ⟨K,hK,hbound⟩ := averagedConditionedRootError_bound hFord hMertens hL hτ hτsmall
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,candidate_root_error_cap hL hτ hτsmall,eventually_ge_atTop 2]
    with B hbound hcap hB
  intro C T H M hT hTs hM0 hM hMexp χ hχ
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p := fun _ hp => (block_prime_twice_sites hB hM hp).1
  have hc := maskedDigitCutError_comparison (by omega : 1 < B) hM χ hsize
    (fun S R => hcap C T H M hM0 hM (primePatternsSites S) χ hχ
      (primeSiteTranspose _ (auxiliaryPrimes B) R))
  have he : arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ
      (arithmeticFirstDigits B u)) =
      finiteExpectation (primeDigitMass B) (maskedDigitCutError B L T H M τ C χ) := by
    exact (prime_square_crt_average B (fun r _ => maskedDigitCutError B L T H M τ C χ r)).trans
      (congrArg (finiteExpectation (primeDigitMass B))
        (funext (fun _ => finiteExpectation_const _ (primeDigitMass_sum B) _)))
  rw [he]
  have hi := hbound C T H M hT hTs hM0 hM hMexp χ hχ
  have hu := (le_abs_self _).trans hc
  linarith only [hi,hu]

end JointDickman

end OAI
