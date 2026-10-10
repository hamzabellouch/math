import OAI.NumberTheory.JointDickman.Amplification.CandidateForwardMass

namespace OAI

/-! # The independent-root fluctuation vanishes after averaging endpoint types -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- The actual endpoint-dependent candidate list has bounded expected
weight per block position. -/
theorem candidateMean_total_mean
    (hFord : FordUpperSieveInput) (hM : PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, χ e ≤ 1) →
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ∑ e : blockCandidates B L T H M τ C (fun i => (S i).val),
          candidateMeanWeight B L τ C (fun i => (S i).val) χ e.val) ≤ K*M := by
  obtain ⟨K,hK,hbound⟩ := latentCandidateKernel_forward_total_mean hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hbound
  intro L T H M τ C hT hTs χ hχ
  have he (S : Fin M → (auxiliaryPrimes B).powerset) :
      (∑ i : Fin M, ∑ k : Fin M,
        if i < k then latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k else 0) =
      ∑ e : blockCandidates B L T H M τ C (fun i => (S i).val),
        candidateMeanWeight B L τ C (fun i => (S i).val) χ e.val := by
    exact candidateMatrix_forward_total
      (fun e : blockCandidates B L T H M τ C (fun i => (S i).val) => e.val.1.1)
      (fun e => e.val.1.2)
      (fun e => candidateMeanWeight B L τ C (fun i => (S i).val) χ e.val)
      (fun e => (mem_blockCandidates.mp e.property).2.1)
  simpa only [he] using hbound L T H M τ C hT hTs χ hχ

noncomputable def averagedIndependentRootError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) : ℝ :=
  finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) (fun S =>
    finiteExpectation (siteProductMass
      (fun _ : blockCandidates B L T H M τ C (fun i => (S i).val) => independentPrimeSetMass B))
      (fun R => kernelCutNorm (fun i k =>
        independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ R i k-
          latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)))

/-- No dependence on the regularity constant C, or on the endpoint types,
remains in the error coefficient. -/
theorem averagedIndependentRootError_bound
    (hFord : FordUpperSieveInput) (hM : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      averagedIndependentRootError B L T H M τ C χ ≤
        K*(B : ℝ)^(-(7/200 : ℝ)) := by
  obtain ⟨K,hK,hmean⟩ := candidateMean_total_mean hFord hM
  refine ⟨3*Real.log 2+4*K,by positivity,?_⟩
  filter_upwards [hmean,actual_candidate_root_fluctuation hL hτ hτsmall] with B hmean hfluc
  intro C T H M hT hTs hM0 χ hχ
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  let f := fun S : Fin M → (auxiliaryPrimes B).powerset =>
    ∑ e : blockCandidates B L T H M τ C (fun i => (S i).val),
      candidateMeanWeight B L τ C (fun i => (S i).val) χ e.val
  let δ : ℝ := (B : ℝ)^(-(7/200 : ℝ))
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  have hwone : (∑ S, w S) = 1 := siteProductMass_sum _ (fun _ => independentPrimeSetMass_sum B)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hm : finiteExpectation w f/(M : ℝ) ≤ K := by
    exact (div_le_iff₀ hMr).mpr (hmean L T H M τ C hT hTs χ (fun e => (hχ e).2))
  calc
    _ ≤ finiteExpectation w (fun S => δ*(3*Real.log 2+4*f S/(M : ℝ))) :=
      finiteExpectation_mono w hw (fun S => hfluc C T H M hM0 (fun i => (S i).val) χ hχ)
    _ = δ*(3*Real.log 2+4*finiteExpectation w f/(M : ℝ)) := by
      simp only [div_eq_mul_inv,finiteExpectation_const_mul,finiteExpectation_add,
        finiteExpectation_mul_const,finiteExpectation_const w hwone]
    _ ≤ δ*(3*Real.log 2+4*K) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      rw [mul_div_assoc]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 4 by norm_num))
    _ = _ := mul_comm _ _

end JointDickman

end OAI
