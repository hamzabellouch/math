import OAI.NumberTheory.JointDickman.Counting.CountingModelEnvelope
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticPatternMeans
import OAI.NumberTheory.JointDickman.Probability.CutNormTriangle
import OAI.NumberTheory.JointDickman.Amplification.CandidateExpectedDegree

namespace OAI

/-! # Transfer of the counting-model error to actual integer sites -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

noncomputable def arithmeticSiteCutMean {B M : ℕ}
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ) : ℝ :=
  arithmeticSquareMean B (fun u => kernelCutNorm
    (realizedSiteKernel K (blockPatternEquiv B M (arithmeticPrimePatterns B M u))))

theorem arithmeticSiteCutMean_comparison {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ x, kernelCutNorm (realizedSiteKernel K x) ≤ C*(B : ℝ)^10) :
    |arithmeticSiteCutMean K -
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel K x))| ≤ 2*C/(B : ℝ) := by
  have hh := arithmeticSquareMean_pattern_comparison hB hM
    (fun p hp => (block_prime_twice_sites (by omega) hM hp).1)
    (fun S => kernelCutNorm (realizedSiteKernel K (blockPatternEquiv B M S))) hC
    (fun S => by rw [abs_of_nonneg (kernelCutNorm_nonneg _)]; exact hcap _)
  simpa only [arithmeticSiteCutMean,Equiv.apply_symm_apply] using hh

theorem latent_model_cut_cap {B L T H M : ℕ} {τ C D : ℝ}
    (hB : 1 ≤ B) (hT : 0 < T) (hM : 0 < M) (hM2 : M ≤ B^2) (hD : 0 ≤ D)
    (χ : BlockCandidateIndex M → ℝ)
    (hcap : ∀ S, (∑ i, ∑ k, |latentCandidateKernel B L T H M τ C S χ i k|) ≤
      2*(M : ℝ)^2*(B : ℝ)^2)
    (J : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (x : Fin M → (auxiliaryPrimes B).powerset) :
    kernelCutNorm (realizedSiteKernel
      (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b) x) ≤
      (2+2*D*Real.exp 24)*(B : ℝ)^10 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hM2r : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM2
  have hlat : (∑ i, ∑ k,
      |realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) x i k|) ≤
      2*(M : ℝ)^2*(B : ℝ)^2 := by
    simpa only [latentPrimeSiteKernel_realizes] using hcap (fun i => (x i).val)
  have hj : (∑ i, ∑ k, |realizedSiteKernel J x i k|) ≤
      (M : ℝ)*(2*D*Real.exp 24) := by
    calc
      _ ≤ ∑ i : Fin M, ∑ k : Fin M, lagEnvelope T D i k :=
        sum_le_sum (fun i _ => sum_le_sum (fun k _ => hJ i k (x i) (x k)))
      _ ≤ ∑ _i : Fin M, (2*D*Real.exp 24) :=
        sum_le_sum (fun i _ => lagEnvelope_row_sum hT hD i)
      _ = _ := by simp
  have hs := (kernel_difference_absolute_mass
    (realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) x)
    (realizedSiteKernel J x)).trans (add_le_add hlat hj)
  calc
    _ ≤ (2*(M : ℝ)^2*(B : ℝ)^2+(M : ℝ)*(2*D*Real.exp 24))/(M : ℝ) := by
      apply (kernelCutNorm_le_absolute_mass _).trans
      simpa only [kernelAbsoluteMass,Fintype.card_fin,realizedSiteKernel] using
        div_le_div_of_nonneg_right hs hMr.le
    _ = 2*(M : ℝ)*(B : ℝ)^2+2*D*Real.exp 24 := by field_simp
    _ ≤ 2*((B : ℝ)^2)*(B : ℝ)^2+2*D*Real.exp 24 := by gcongr
    _ = 2*(B : ℝ)^4+2*D*Real.exp 24 := by ring
    _ ≤ 2*(B : ℝ)^10+(2*D*Real.exp 24)*(B : ℝ)^10 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hBr (by norm_num : 4 ≤ 10)) (by norm_num)
      · exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hBr)
    _ = _ := by ring

theorem latent_model_arithmetic_comparison {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T → 0 < M → M ≤ B^2 →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ J : Fin M → Fin M → (auxiliaryPrimes B).powerset →
        (auxiliaryPrimes B).powerset → ℝ,
      (∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k) →
      |arithmeticSiteCutMean
        (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b)-
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => kernelCutNorm (realizedSiteKernel
            (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b) x))| ≤
        2*(2+2*D*Real.exp 24)/(B : ℝ) := by
  filter_upwards [candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2]
    with B hcap hB
  intro C T H M hT hM hM2 χ hχ J hJ
  apply arithmeticSiteCutMean_comparison (by omega) hM2 _ (by positivity)
  exact latent_model_cut_cap (by omega) hT hM hM2 hD χ
    (fun S => (hcap C T H M S χ hχ).1) J hJ

end JointDickman

end OAI
