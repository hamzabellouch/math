import OAI.NumberTheory.JointDickman.Counting.CountingSampling
import OAI.NumberTheory.JointDickman.Counting.CountingKernelBound
import OAI.NumberTheory.JointDickman.Counting.CountingSlowMean

namespace OAI

/-! # The published sampling inputs control the actual moving arithmetic error -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_slow_mean
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (H M U V Q : ℕ),
        Cmin ≤ C →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → amplificationMultiplier B*Q ≤ B →
        η*amplificationMultiplier B ≤ H → amplificationMultiplier B ≤ M →
        c₁*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U₁*(B : ℝ)^(0.32 : ℝ) →
        M ≤ B^2 →
        FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
        ∀ (J : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ N : ℕ in atTop,
        ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
        (∀ b r, r < auxiliarySquarePeriod B →
          |σ (b*auxiliarySquarePeriod B+r)-σ (b*auxiliarySquarePeriod B)| ≤
            (auxiliarySquarePeriod B : ℝ)/((amplificationMultiplier B : ℝ)*(N+1))) →
        (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
          H M τ C w c D (σ u) u)/(N : ℝ) < (J : ℝ)*(ε+Kerror/(B : ℝ))+δ := by
  obtain ⟨τ,hτ,hτcap,hτsmall,hsample⟩ := counting_sampling hFord hSD hSW hM hMP hL hη hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w c₁ U₁ ε hw hc₁ hU₁ hε
  obtain ⟨P,c,hc,D,m,hm,Cmin,hCmin,hmodel⟩ := hsample w c₁ U₁ ε hw hc₁ hU₁ hε
  obtain ⟨V,hV,hbound⟩ := countingPrimeKernel_bounded hM hMP P m hm c (fun d => (hc d).1) D
  obtain ⟨K,hK,hvariation⟩ := countingPrimeKernel_parameter_variation hM hMP P m hm c
    (fun d => (hc d).1) D hη
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  let E := R*V/η
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let Kerror := 2*(2+2*E*Real.exp 24)
  refine ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,by dsimp [Kerror]; positivity,?_⟩
  filter_upwards [hmodel,hbound,hvariation,hroot,amplification_sampling_scale,
    latent_model_arithmetic_comparison (by omega : 1 ≤ L) hτ.le hτsmall hE,
    candidate_kernels_polynomial_mass (by omega : 1 ≤ L) hτ.le hτsmall]
    with B hmodel hbound hvariation hroot hscale hcompare hmass
  intro C H M U V₀ Q hC hU hV₀ hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hM2 hMC J δ hδ
  let T := amplificationMultiplier B
  have hT : 0 < T := hscale.1
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : Real.log (T : ℝ) ≤ (B : ℝ)/10 := hscale.2.2.2.2.1
  have hMp : 0 < M := hT.trans_le hTM
  have hmean (σ : ℝ) (hσ : |σ| ≤ 3) : arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ) ≤ ε+Kerror/(B : ℝ) := by
    have he := hmodel C H M U V₀ Q hC hU hV₀ hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hMC σ hσ
    have hc' := hcompare C T H M hT hMp hM2 (rampedCandidateCutoff B T w σ)
      (rampedCandidateCutoff_bounds hw B T σ) (countingSiteModel P m B L T H M τ C c D σ)
      (countingSiteModel_uniform_envelope hMP P m B L T H M τ C c D hT hη hV
        (hroot L τ C) hH (fun j _ _ => hbound j T σ hT1 hlog hσ))
    have hdiff := le_abs_self (arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ)-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel
          (countingSiteError P m B L T H M τ C w c D σ) x)))
    change |arithmeticSiteCutMean (countingSiteError P m B L T H M τ C w c D σ)-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel
          (countingSiteError P m B L T H M τ C w c D σ) x))| ≤ Kerror/(B : ℝ) at hc'
    linarith
  have hmass' (x : Fin M → (auxiliaryPrimes B).powerset) :
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ 2*(M : ℝ)*(B : ℝ)^2 := by
    have hχ : ∀ e : BlockCandidateIndex M, 0 ≤ smoothCandidateCutoff B T e ∧ smoothCandidateCutoff B T e ≤ 1 := by
      intro e
      refine ⟨smoothCandidateCutoff_nonneg B T e,?_⟩
      unfold smoothCandidateCutoff candidateCutoff amplificationOuterWeight amplificationInnerWeight
      exact (mul_le_mul (mul_le_mul (amplificationBump_bounds _).2 (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num)) (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num)).trans_eq (by norm_num)
    have hh := (hmass C T H M (fun i => (x i).val) (smoothCandidateCutoff B T) hχ).1
    unfold kernelAbsoluteMass
    simp only [Fintype.card_fin]
    apply (div_le_div_of_nonneg_right hh (Nat.cast_nonneg M)).trans_eq
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hMp.ne'
    field_simp
  exact counting_slow_mean P m B L T H M τ C w c D (by positivity) hK
    (by positivity : 0 ≤ ε+Kerror/(B : ℝ)) hw hT hMp hmass'
    (fun j s t hj hjT hs ht => hvariation j T s t hT1 hlog
      (hH.trans (by exact_mod_cast hj.le)) hs ht) hmean J hδ

end JointDickman

end OAI
