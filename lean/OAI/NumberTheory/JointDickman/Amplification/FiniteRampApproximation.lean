import OAI.NumberTheory.JointDickman.Counting.OriginRampAverage

namespace OAI

/-! # Replacing the exact counting cutoff by a common block-origin ramp -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteRampCutError (B L T H M N u : ℕ) (τ C δ : ℝ) : ℝ :=
  kernelCutNorm (fun i k =>
    latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (finiteCandidateCutoff B T N u) i k-
    latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
      (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k)

theorem finite_ramp_approximation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C δ : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → 0 < M → M ≤ B^2 → 0 < δ →
      ∀ (J : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ J*N →
        (∑ u ∈ range K, finiteRampCutError B L T H M N u τ C δ)/(N : ℝ) <
          A*(T : ℝ)*δ+ε := by
  obtain ⟨A,hA,hmean⟩ := baseCandidateMassMean_bound hFord hMertens hL hτ hτsmall
  refine ⟨2*A,by positivity,?_⟩
  filter_upwards [hmean,candidate_kernels_polynomial_mass hL hτ hτsmall] with B hb hm
  intro T H M C δ hT hTs hM hM2 hδ J ε hε
  have hχ : ∀ e : BlockCandidateIndex M,
      0 ≤ smoothCandidateCutoff B T e ∧ smoothCandidateCutoff B T e ≤ 1 := by
    intro e
    refine ⟨smoothCandidateCutoff_nonneg B T e,?_⟩
    change amplificationBump _*amplificationBump _*amplificationBump _ ≤ 1
    exact (mul_le_mul
      (mul_le_mul (amplificationBump_bounds _).2 (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num))
      (amplificationBump_bounds _).2 (amplificationBump_bounds _).1 (by norm_num)).trans_eq
      (by norm_num)
  have hhalf : 0 < ε/2 := by linarith
  filter_upwards [finite_endpoint_cutNorm_mean (B := B) (L := L) (H := H)
      (τ := τ) (C := C) hT hM hδ hhalf,
    origin_ramp_average_zero hT hδ hM
      (by positivity : (0 : ℝ) ≤ 2*(M : ℝ)^2*(B : ℝ)^2)
      (fun S => (hm C T H M S (smoothCandidateCutoff B T) hχ).1) J hhalf] with N hn ho
  intro K hK
  have ht : (∑ u ∈ range K, finiteRampCutError B L T H M N u τ C δ)/(N : ℝ) ≤
      (∑ u ∈ range K, kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (finiteCandidateCutoff B T N u) i k-
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (endpointRampedCutoff B T N u δ) i k))/(N : ℝ)+
      (∑ u ∈ range K, kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (endpointRampedCutoff B T N u δ) i k-
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k))/(N : ℝ) := by
    rw [← add_div,← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact sum_le_sum (fun _ _ => kernelCutNorm_sub_triangle _ _ _)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hbase : (2*(T : ℝ)*δ/(M : ℝ))*baseCandidateMassMean B L T H M τ C ≤
      2*A*(T : ℝ)*δ := by
    apply (mul_le_mul_of_nonneg_left (hb T H M C hT hTs hM hM2) (by positivity)).trans_eq
    field_simp
  have hnK := hn K
  have hoK := ho K hK
  linarith

end JointDickman

end OAI
