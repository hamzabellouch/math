import OAI.NumberTheory.JointDickman.Amplification.FiniteRampWeights

namespace OAI

/-! # Averaged error mass of the hard counting cutoff over the finite candidate pool -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointRampErrorMass (B L T H M N u : ℕ) (τ C δ : ℝ) : ℝ :=
  ∑ e ∈ primeCandidatePool B M, baseCandidateContribution B L T H M τ C e u*
    |(if ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) <
        (candidateLow e : ℝ)/(T*candidateQuotient e) then 1 else 0)-
      countingRamp δ (((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)))
        ((candidateLow e : ℝ)/(T*candidateQuotient e))|

noncomputable def baseCandidateMassMean (B L T H M : ℕ) (τ C : ℝ) : ℝ :=
  ∑ e ∈ primeCandidatePool B M,
    (∑ r, residueBaseContribution B L T H M τ C e r)/(auxiliarySquarePeriod B : ℝ)

open Classical in
theorem endpointRampErrorMass_mean {B L T H M : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (∑ u ∈ range K, endpointRampErrorMass B L T H M N u τ C δ)/(N : ℝ) <
        (T : ℝ)*δ*baseCandidateMassMean B L T H M τ C+ε := by
  let I := primeCandidatePool B M
  let e0 := ε/((I.card : ℝ)+1)
  have he0 : 0 < e0 := div_pos hε (by positivity)
  have hb (e : BlockCandidateIndex M) :=
    baseCandidateContribution_ramp_error (B := B) (L := L) (H := H) (τ := τ) (C := C) hT hδ e he0
  filter_upwards [(eventually_all_finset I).mpr (fun e _ => hb e)] with N hN
  intro K
  unfold endpointRampErrorMass
  rw [sum_comm,sum_div]
  calc
    _ ≤ ∑ e ∈ I, ((T : ℝ)*δ*
        ((∑ r, residueBaseContribution B L T H M τ C e r)/(auxiliarySquarePeriod B : ℝ))+e0) :=
      sum_le_sum (fun e he => (hN e he K).le)
    _ = (T : ℝ)*δ*baseCandidateMassMean B L T H M τ C+(I.card : ℝ)*e0 := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul]
      simp only [baseCandidateMassMean,I,mul_sum]
    _ < _ := by
      have hc : (I.card : ℝ)*e0 < ε := by
        dsimp [e0]
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (I.card : ℝ)+1)).mpr
        nlinarith
      linarith

open Classical in
theorem finite_endpoint_cutNorm_bound {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) :
    kernelCutNorm (fun i k =>
      latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
        (finiteCandidateCutoff B T N u) i k-
      latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
        (endpointRampedCutoff B T N u δ) i k) ≤
      (2*endpointRampErrorMass B L T H M N u τ C δ)/(M : ℝ) := by
  apply (latentCandidateKernel_cutNorm_sub B L T H M τ C _ _ _).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [sum_coe_sort (blockCandidates B L T H M τ C
    (fun j => coefficientPrimeSet B (u+(j.val+1))))
    (fun e => |candidateMeanWeight B L τ C
      (fun j => coefficientPrimeSet B (u+(j.val+1))) (finiteCandidateCutoff B T N u) e-
      candidateMeanWeight B L τ C
      (fun j => coefficientPrimeSet B (u+(j.val+1))) (endpointRampedCutoff B T N u δ) e|)]
  let S := fun j : Fin M => coefficientPrimeSet B (u+(j.val+1))
  have hsub := blockCandidates_subset_primePool (B := B) (L := L) (T := T) (H := H)
    (τ := τ) (C := C) (S := S) (fun _ => filter_subset _ _)
  calc
    _ = ∑ e ∈ blockCandidates B L T H M τ C S,
        baseCandidateContribution B L T H M τ C e u*
          |(if ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) <
              (candidateLow e : ℝ)/(T*candidateQuotient e) then 1 else 0)-
            countingRamp δ (((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)))
              ((candidateLow e : ℝ)/(T*candidateQuotient e))| := by
      apply sum_congr rfl
      intro e he
      exact finite_endpoint_weight_error hT e he
    _ = endpointRampErrorMass B L T H M N u τ C δ := by
      unfold endpointRampErrorMass
      apply sum_subset hsub
      intro e _ he
      dsimp only [S] at he
      simp only [baseCandidateContribution,ite_eq_right he,zero_mul]
    _ ≤ _ := le_rfl

open Classical in
theorem finite_endpoint_cutNorm_mean {B L T H M : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (∑ u ∈ range K, kernelCutNorm (fun i k =>
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (finiteCandidateCutoff B T N u) i k-
        latentCandidateKernel B L T H M τ C (fun j => coefficientPrimeSet B (u+(j.val+1)))
          (endpointRampedCutoff B T N u δ) i k))/(N : ℝ) <
        (2*(T : ℝ)*δ/(M : ℝ))*baseCandidateMassMean B L T H M τ C+ε := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  filter_upwards [endpointRampErrorMass_mean (B := B) (L := L) (H := H) (M := M)
    (τ := τ) (C := C) hT hδ (mul_pos hε (div_pos hMr (by norm_num : (0 : ℝ) < 2)))] with N hN
  intro K
  have hh := mul_lt_mul_of_pos_left (hN K) (div_pos (by norm_num : (0 : ℝ) < 2) hMr)
  calc
    _ ≤ (2/(M : ℝ))*((∑ u ∈ range K, endpointRampErrorMass B L T H M N u τ C δ)/(N : ℝ)) := by
      have hh := sum_le_sum (fun u (_ : u ∈ range K) =>
        finite_endpoint_cutNorm_bound (B := B) (L := L) (H := H) (M := M) (N := N)
          (u := u) (τ := τ) (C := C) (δ := δ) hT)
      apply (div_le_div_of_nonneg_right hh (Nat.cast_nonneg N)).trans_eq
      simp only [div_eq_mul_inv,mul_sum,sum_mul]
      apply sum_congr rfl
      intro u _
      ring
    _ < _ := by
      convert hh using 1
      field_simp

end JointDickman

end OAI
