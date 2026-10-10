import OAI.NumberTheory.JointDickman.Amplification.BaseCandidateMass

namespace OAI

/-! # A uniform bound on the mean mass in the counting-cutoff error -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem baseCandidateMassMean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 →
      baseCandidateMassMean B L T H M τ C ≤ K*(M : ℝ) := by
  obtain ⟨K,hK,hrow⟩ := candidateSiteKernel_expected_degree hFord hMertens
  refine ⟨K+4,by positivity,?_⟩
  filter_upwards [hrow,candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2]
    with B hrow hmass hB
  intro T H M C hT hTs hM hM2
  let χ : BlockCandidateIndex M → ℝ := smoothCandidateCutoff B T
  have hχ : ∀ e, 0 ≤ χ e ∧ χ e ≤ 1 := by
    intro e
    refine ⟨smoothCandidateCutoff_nonneg B T e,?_⟩
    change amplificationBump _*amplificationBump _*amplificationBump _ ≤ 1
    exact (mul_le_mul
      (mul_le_mul (amplificationBump_bounds _).2 (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num))
      (amplificationBump_bounds _).2 (amplificationBump_bounds _).1 (by norm_num)).trans_eq
      (by norm_num)
  let F (S : BlockPrimePatterns B M) : ℝ :=
    ∑ i, ∑ k, latentCandidateKernel B L T H M τ C (primePatternsSites S) χ i k
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hF : ∀ S, |F S| ≤ 2*(B : ℝ)^10 := by
    intro S
    calc
      _ ≤ ∑ i : Fin M, ∑ k : Fin M,
          |latentCandidateKernel B L T H M τ C (primePatternsSites S) χ i k| :=
        (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _))
      _ ≤ 2*(M : ℝ)^2*(B : ℝ)^2 := (hmass C T H M (primePatternsSites S) χ hχ).1
      _ ≤ 2*((B : ℝ)^2)^2*(B : ℝ)^2 := by
        gcongr
        exact_mod_cast hM2
      _ = 2*(B : ℝ)^6 := by ring
      _ ≤ 2*(B : ℝ)^10 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hB1 (by norm_num : 6 ≤ 10)) (by norm_num)
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p :=
    fun p hp => (block_prime_twice_sites hB hM2 hp).1
  have hc := arithmeticSquareMean_pattern_comparison (by omega : 1 < B) hM2 hsize
    F (by norm_num : (0 : ℝ) ≤ 2) hF
  have he : finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => F ((blockPatternEquiv B M).symm S)) ≤ (M : ℝ)*K := by
    have hv (S : Fin M → (auxiliaryPrimes B).powerset) :
        primePatternsSites ((blockPatternEquiv B M).symm S) = (fun j => (S j).val) := by
      funext j
      rw [← blockPatternEquiv_val,Equiv.apply_symm_apply]
    simp_rw [F,hv]
    exact latentCandidateKernel_mean_total_le χ (fun i a =>
      hrow L T H M τ C hT hTs χ (fun e => (hχ e).2) i a.val (mem_powerset.mp a.property))
  have ha : arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u)) ≤
      (M : ℝ)*K+4/(B : ℝ) := by
    have hh := (le_abs_self _).trans hc
    linarith
  have hb : baseCandidateMassMean B L T H M τ C =
      arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u))/2 := by
    rw [baseCandidateMassMean_eq]
    have hv (u : ℕ) : primePatternsSites (arithmeticPrimePatterns B M u) =
        (fun j => coefficientPrimeSet B (u+(j.val+1))) :=
      funext (primePatternsSites_arithmetic B M u)
    simp only [F,hv,χ,arithmeticSquareMean,div_eq_mul_inv,mul_sum,mul_comm,mul_left_comm]
  rw [hb]
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hfrac : 4/(B : ℝ) ≤ 4 := div_le_self (by norm_num) hB1
  nlinarith

end JointDickman

end OAI
