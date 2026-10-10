import OAI.NumberTheory.JointDickman.Counting.OriginRampShift

namespace OAI

/-! # The endpoint-to-origin ramp error has zero long-average limit -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem origin_ramp_average_zero {B L T H M : ℕ} {τ C δ A : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hM : 0 < M) (hA : 0 ≤ A)
    (hbound : ∀ S : Fin M → Finset ℕ,
      (∑ i, ∑ k, |latentCandidateKernel B L T H M τ C S (smoothCandidateCutoff B T) i k|) ≤ A)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ J*N →
      (∑ u ∈ range K, kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (endpointRampedCutoff B T N u δ) i k-
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k))/(N : ℝ) < ε := by
  let c := (J : ℝ)*A/((T : ℝ)*δ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) c
  filter_upwards [hlim.eventually (Iio_mem_nhds hε),eventually_gt_atTop 0] with N hN hN0
  intro K hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hbound' (u : ℕ) : kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (endpointRampedCutoff B T N u δ) i k-
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k) ≤
      A/((T : ℝ)*(N+1)*δ) := by
    apply (endpoint_origin_cutNorm_bound hT hδ _).trans
    have h := div_le_div_of_nonneg_right (hbound (fun j => coefficientPrimeSet B (u+(j.val+1)))) hMr.le
    have h' : kernelAbsoluteMass (latentCandidateKernel B L T H M τ C
      (fun j => coefficientPrimeSet B (u+(j.val+1))) (smoothCandidateCutoff B T)) ≤ A/(M : ℝ) := by
      simpa only [kernelAbsoluteMass,Fintype.card_fin] using h
    apply (mul_le_mul_of_nonneg_left h' (by positivity :
      (0 : ℝ) ≤ (M : ℝ)/((T : ℝ)*(N+1)*δ))).trans_eq
    field_simp
  calc
    _ ≤ ((K : ℝ)*(A/((T : ℝ)*(N+1)*δ)))/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNr.le
      exact (sum_le_sum (fun u _ => hbound' u)).trans_eq (by simp)
    _ ≤ (((J : ℝ)*N)*(A/((T : ℝ)*(N+1)*δ)))/(N : ℝ) := by
      gcongr
      exact_mod_cast hK
    _ = c/((N : ℝ)+1) := by dsimp [c]; field_simp
    _ ≤ c/(N : ℝ) := div_le_div_of_nonneg_left hc hNr (by linarith)
    _ < ε := hN

end JointDickman

end OAI
