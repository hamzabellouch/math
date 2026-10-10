import OAI.NumberTheory.JointDickman.Amplification.LatentContributionCap

namespace OAI

/-! # Keeping representation multiplicity in the latent second moment -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidatePairRepresentations (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i k : Fin M) (S R : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((endpointSplits B L τ C S).product (endpointSplits B L τ C R)).filter
    (fun ab => BlockCandidateAdmissible B L T H τ C ((i,k),ab))

theorem latentCandidateKernel_representation_sum (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i k (S i) (S k),
        candidateMeanWeight B L τ C S χ ((i,k),ab) := by
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  simp only [candidatePairRepresentations,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]

/-- The multiplicity factor must be averaged with a first representation;
replacing it by one would incorrectly discard collisions on an edge. -/
theorem latentCandidateKernel_square_multiplicity
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ i k : Fin M, i < k →
      (latentCandidateKernel B L T H M τ C S χ i k)^2 ≤
        (B : ℝ)^(-(22/100 : ℝ))*
          (candidatePairRepresentations B L T H τ C i k (S i) (S k)).card*
          latentCandidateKernel B L T H M τ C S χ i k := by
  filter_upwards [candidateMeanWeight_small hM hL hτ hτsmall] with B hcap
  intro C T H M S χ hχ i k hik
  have hnn := latentCandidateKernel_nonneg B L T H M τ C S χ (fun e => (hχ e).1) i k
  have hbound : latentCandidateKernel B L T H M τ C S χ i k ≤
      (B : ℝ)^(-(22/100 : ℝ))*
        (candidatePairRepresentations B L T H τ C i k (S i) (S k)).card := by
    rw [latentCandidateKernel_representation_sum B L T H M τ C S χ i k hik]
    calc
      _ ≤ ∑ _ab ∈ candidatePairRepresentations B L T H τ C i k (S i) (S k),
          (B : ℝ)^(-(22/100 : ℝ)) :=
        sum_le_sum (fun ab _ => hcap C M S χ (fun e => (hχ e).2) ((i,k),ab))
      _ = _ := by simp [mul_comm]
  nlinarith [mul_le_mul_of_nonneg_right hbound hnn]

end JointDickman

end OAI
