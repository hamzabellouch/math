import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootTests
import OAI.NumberTheory.JointDickman.Amplification.CandidateRootErrorCap
import OAI.NumberTheory.JointDickman.Amplification.AveragedRootFluctuation

namespace OAI

/-! # The site-conditioned auxiliary roots have vanishing fluctuations -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

noncomputable def averagedConditionedRootError (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) : ℝ :=
  finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) (fun S =>
    finiteExpectation
      (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (fun i => (S i).val))
        (fun i => (S i).val))
      (fun R => kernelCutNorm (fun i k =>
        independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ
          (primeSiteTranspose (blockCandidates B L T H M τ C (fun i => (S i).val)) (auxiliaryPrimes B) R) i k-
        latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)))

theorem averagedConditionedRootError_bound
    (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 →
      (M : ℝ) ≤ Real.exp B → ∀ χ : BlockCandidateIndex M → ℝ,
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      averagedConditionedRootError B L T H M τ C χ ≤
        K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B := by
  obtain ⟨K,hK,hind⟩ := averagedIndependentRootError_bound hFord hMertens hL hτ hτsmall
  refine ⟨K,hK,?_⟩
  filter_upwards [hind,averaged_siteConditionedRoot_test hL hτ hτsmall,
    candidate_root_error_cap hL hτ hτsmall] with B hind htest hcap
  intro C T H M hT hTs hM0 hM hMexp χ hχ
  have hTe : (T : ℝ) ≤ Real.exp B := hTs.trans (Real.exp_le_exp.mpr (by
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith))
  let F := fun (S : Fin M → (auxiliaryPrimes B).powerset)
    (R : blockCandidates B L T H M τ C (fun i => (S i).val) → (auxiliaryPrimes B).powerset) =>
    kernelCutNorm (fun i k => independentCandidateKernel B L T H M τ C (fun i => (S i).val) χ R i k-
      latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k)
  have hc := htest C T H M hT hTe hMexp hM F
    (fun S R => hcap C T H M hM0 hM (fun i => (S i).val) χ hχ R)
  change |averagedConditionedRootError B L T H M τ C χ-
    averagedIndependentRootError B L T H M τ C χ| ≤ (B : ℝ)^10*conditionedRootError B at hc
  have hi := hind C T H M hT hTs hM0 χ hχ
  have hl := (le_abs_self (averagedConditionedRootError B L T H M τ C χ-
    averagedIndependentRootError B L T H M τ C χ)).trans hc
  linarith only [hl,hi]

end JointDickman

end OAI
