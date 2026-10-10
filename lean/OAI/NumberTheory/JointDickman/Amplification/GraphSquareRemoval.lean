import OAI.NumberTheory.JointDickman.Probability.FiniteGraphKernel
import OAI.NumberTheory.JointDickman.Probability.CutNormTriangle

namespace OAI

/-! # Removing square-hit blocks from the original finite graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteGraphCandidateError (B L T H M N u : ℕ) (τ C : ℝ) : ℝ :=
  kernelCutNorm (fun i k => finiteGraphKernel B L T H M N u τ C i k-
    actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k)

noncomputable def finiteGraphLatentError (B L T H M N u : ℕ) (τ C : ℝ) : ℝ :=
  kernelCutNorm (fun i k => finiteGraphKernel B L T H M N u τ C i k-
    latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u) i k)

theorem finiteGraphCandidateError_zero {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hsq : ¬ BlockSquareHit B M u) :
    finiteGraphCandidateError B L T H M N u τ C = 0 := by
  unfold finiteGraphCandidateError
  rw [finiteGraphKernel_eq_candidate hB hT hTP hsq]
  simp only [sub_self]
  exact kernelCutNorm_zero

theorem finiteGraphCandidateError_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M N u : ℕ), 0 < T → 0 < M → M ≤ B^2 →
      finiteGraphCandidateError B L T H M N u τ C ≤ (B : ℝ)^10 := by
  filter_upwards [finiteGraphKernel_entry_cap hL hτ hτsmall,
    candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2] with B hfg hmass hB
  intro C T H M N u hT hM0 hM
  let G := finiteGraphKernel B L T H M N u τ C
  let A := actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u
  have hg : (∑ i, ∑ k, |G i k|) ≤ (M : ℝ)^2*(B : ℝ)^2 := by
    calc
      _ ≤ ∑ _i : Fin M, ∑ _k : Fin M, (B : ℝ)^2 :=
        sum_le_sum (fun i _ => sum_le_sum (fun k _ => hfg C T H M N u hT i k))
      _ = _ := by simp [pow_two,mul_assoc]
  have ha : (∑ i, ∑ k, |A i k|) ≤ 2*(M : ℝ)^2*(B : ℝ)^2 :=
    (hmass C T H M (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u) (finiteCandidateCutoff_bounds B T N u)).2
      (primeSiteTranspose _ (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u)))
  have hd : (∑ i, ∑ k, |G i k-A i k|) ≤ 3*(M : ℝ)^2*(B : ℝ)^2 :=
    (kernel_difference_absolute_mass G A).trans (by linarith)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
  have hm2 : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hb2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hb1 : (1 : ℝ) ≤ B := by linarith
  have hb4 : (3 : ℝ) ≤ (B : ℝ)^4 := by
    have hs : (4 : ℝ) ≤ (B : ℝ)^2 := by nlinarith
    exact (by linarith : (3 : ℝ) ≤ (B : ℝ)^2).trans
      (pow_le_pow_right₀ hb1 (by norm_num : 2 ≤ 4))
  change kernelCutNorm (fun i k => G i k-A i k) ≤ _
  calc
    _ ≤ kernelAbsoluteMass (fun i k => G i k-A i k) := kernelCutNorm_le_absolute_mass _
    _ ≤ (3*(M : ℝ)^2*(B : ℝ)^2)/(M : ℝ) := by
      simpa only [kernelAbsoluteMass,Fintype.card_fin] using
        div_le_div_of_nonneg_right hd (Nat.cast_nonneg M)
    _ ≤ 3*(M : ℝ)^2*(B : ℝ)^2 := div_le_self (by positivity) hm1
    _ ≤ 3*((B : ℝ)^2)^2*(B : ℝ)^2 := by gcongr
    _ = 3*(B : ℝ)^6 := by ring
    _ ≤ (B : ℝ)^4*(B : ℝ)^6 := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = _ := by ring

theorem finiteGraphLatentError_pointwise {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hcap : finiteGraphCandidateError B L T H M N u τ C ≤ (B : ℝ)^10) :
    finiteGraphLatentError B L T H M N u τ C ≤
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u+
        (B : ℝ)^10*(if BlockSquareHit B M u then 1 else 0) := by
  have ht := kernelCutNorm_sub_triangle (finiteGraphKernel B L T H M N u τ C)
    (actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u)
    (latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u))
  change finiteGraphLatentError B L T H M N u τ C ≤
    finiteGraphCandidateError B L T H M N u τ C+
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u at ht
  by_cases hs : BlockSquareHit B M u
  · simp only [hs,ite_true,mul_one]
    linarith
  · rw [finiteGraphCandidateError_zero hB hT hTP hs] at ht
    simpa only [hs,ite_false,mul_zero,add_zero,zero_add] using ht

end JointDickman

end OAI
