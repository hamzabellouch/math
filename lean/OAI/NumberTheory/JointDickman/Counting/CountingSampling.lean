import OAI.NumberTheory.JointDickman.Counting.CountingModelEnvelope
import OAI.NumberTheory.JointDickman.Counting.CountingBlockTest
import OAI.NumberTheory.JointDickman.Counting.SamplingLagModel
import OAI.NumberTheory.JointDickman.Probability.LatentMassMoments

namespace OAI

/-! # Sampling the actual latent counting graph and its finite-feature model -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin : ℝ, 0 ≤ Cmin ∧
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
        FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
        ∀ σ : ℝ, |σ| ≤ 3 →
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => kernelCutNorm (realizedSiteKernel
            (countingSiteError P m B L (amplificationMultiplier B) H M τ C w c D σ) x)) ≤ ε := by
  obtain ⟨τ,q,hτ,hτcap,hτsmall,hq,hquad⟩ :=
    latentPrimeSiteKernel_row_square_mass hFord hM hL (show 0 < η/2 by positivity) hcap
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  obtain ⟨J,hJ,hrow⟩ := latentPrimeSiteKernel_row_mean hFord hM
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w c₁ U₁ ε hw hc₁ hU₁ hε
  let δ := ε/(12*Real.exp 24)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,e,he0,he,hblock⟩ :=
    counting_block_test hFord hSD hSW hM hMP (by omega : 0 < L) hτ hη hw hδ
  let Cmin := max 0 (10*Real.log ((K+1)/δ))
  have hCmin : 0 ≤ Cmin := le_max_left _ _
  have htail : ∀ C : ℝ, Cmin ≤ C → K*Real.exp (-(1/10 : ℝ)*C) ≤ δ := by
    intro C hC
    have hh : 10*Real.log ((K+1)/δ) ≤ C := (le_max_right _ _).trans hC
    have hexp := Real.exp_le_exp.mpr (show -(1/10 : ℝ)*C ≤ -Real.log ((K+1)/δ) by linarith)
    calc
      _ ≤ (K+1)*Real.exp (-(1/10 : ℝ)*C) := by gcongr; linarith
      _ ≤ (K+1)*Real.exp (-Real.log ((K+1)/δ)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      _ = δ := by
        rw [Real.exp_neg,Real.exp_log (by positivity : 0 < (K+1)/δ)]
        field_simp
  have hsample := sampling_lag_model hJ.le hq.le
    (show 0 ≤ R*C₀/η by positivity) hc₁ hU₁ (show 0 ≤ ε/2 by positivity)
    (show 0 < ε/2 by positivity)
  refine ⟨P,c,hc,D,m,hm,Cmin,hCmin,?_⟩
  filter_upwards [hquad,hroot,hrow,hblock,hsample,amplification_sampling_scale,
    he.eventually (eventually_le_nhds hδ)] with B hquad hroot hrow hblock hsample hscale heB
  intro C H M U V Q hC hU hV hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hMC σ hσ
  let T := amplificationMultiplier B
  have hT : 0 < T := hscale.1
  have hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := hscale.2.1
  have hH' : (η/2)*(B : ℝ)^(32/100 : ℝ) ≤ H := by
    calc
      _ = η*((B : ℝ)^(32/100 : ℝ)/2) := by ring
      _ ≤ η*(T : ℝ) := mul_le_mul_of_nonneg_left hscale.2.2.2.2.2 hη.le
      _ ≤ _ := hH
  have hMpos : 0 < M := hT.trans_le hTM
  have hχ := rampedCandidateCutoff_bounds hw B T σ (M := M)
  obtain ⟨hbound,htest⟩ := hblock C T H M U V Q (hCmin.trans hC) hT le_rfl
    hscale.2.2.2.2.1 hU hV hdyU hdyV hQ hcut hTQ hH hTM σ hσ
  have htestsmall : 2*(e B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24 ≤ ε/2 := by
    calc
      _ ≤ 2*(δ+δ+δ)*Real.exp 24 := by gcongr; exact htail C hC
      _ = _ := by dsimp [δ]; field_simp; ring
  have hs := hsample M (auxiliaryPrimes B).powerset hMpos hMC
    (fun _ : Fin M => independentPrimeSetMass B)
    (fun _ => independentPrimeSetMass_nonneg B) (fun _ => independentPrimeSetMass_sum B)
    (latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ))
    (countingSiteModel P m B L T H M τ C c D σ)
    (fun i j a b => candidateSiteKernel_symm _ _ _ _ _ _ _ _ _ _ _ _)
    (countingSiteModel_symm P m B L T H M τ C c D σ)
    (fun i a => candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _)
    (fun i a => countingSiteModel_diag P m B L T H M τ C c D σ i a a)
    (fun i j a b => candidateSiteKernel_nonneg _ _ _ _ _ _ _ _
      (fun e => (hχ e).1) _ _ _ _)
    (countingSiteModel_uniform_envelope hMP P m B L T H M τ C c D hT hη hC₀
      (hroot L τ C) hH hbound) hMlo hMhi
    (hrow L T H M τ C hT hTs _ hχ)
    (by simpa only [show -(21/100 : ℝ) = (-0.21 : ℝ) by norm_num] using
      hquad T H M C hT hTs hscale.2.2.1 hscale.2.2.2.1 hH' _ hχ)
    (fun g h hg hh => (htest g h hg hh).trans
      (mul_le_mul_of_nonneg_left htestsmall (Nat.cast_nonneg M)))
  change finiteExpectation _ (fun x => kernelCutNorm
    (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D σ) x)) ≤ ε/2+ε/2 at hs
  rw [add_halves] at hs
  exact hs

end JointDickman

end OAI
