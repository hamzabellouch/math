import OAI.Probability.SLE.Geometry.HarmonicExitLimit
import OAI.Probability.SLE.Stochastic.PlanarHolomorphicTests

namespace OAI

/-! A bounded holomorphic map has a genuine left limit at each finite
exit of the original planar Wiener path from its open domain. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

theorem holomorphic_domain_exit_limit
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) (hw : w∈D) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D)
    (T : ℝ≥0) (C : ℝ≥0) (hC : ∀ z∈D, ‖F z‖ ≤ C) :
    ∀ᵐ b ∂W.prod W, ∀ τ : ℝ≥0, τ ≤ T →
      (∀ t<τ, w+Complex.equivRealProdCLM.symm (planarWiener t b)∈D) →
      w+Complex.equivRealProdCLM.symm (planarWiener τ b)∉D →
      ∃ c : ℂ, Tendsto (fun t => F (w+Complex.equivRealProdCLM.symm (planarWiener t b)))
        (𝓝[<] τ) (𝓝 c) := by
  have hU := planarTranslatedDomain_open hD w
  have h0 : (0:ℝ×ℝ)∈planarTranslatedDomain D w := by simpa [planarTranslatedDomain] using hw
  let e := Classical.choice (exists_smoothDomainExhaustion _ hU 0 h0)
  obtain ⟨⟨hr,hr0⟩,⟨hi,hi0⟩⟩ := holomorphic_planar_components hD hF w
  obtain ⟨Yr,_,_,_,_,hYr⟩ := e.harmonic_exit_limit W hW T hU _ hr hr0 C
    (fun z hz => (Complex.abs_re_le_norm _).trans (hC _ hz))
  obtain ⟨Yi,_,_,_,_,hYi⟩ := e.harmonic_exit_limit W hW T hU _ hi hi0 C
    (fun z hz => (Complex.abs_im_le_norm _).trans (hC _ hz))
  filter_upwards [hYr,hYi] with b hb hi
  intro τ hτ hp hx
  have hrl := hb τ hτ hp hx
  have hil := hi τ hτ hp hx
  refine ⟨Complex.equivRealProdCLM.symm (Yr b,Yi b),?_⟩
  have hh := Complex.equivRealProdCLM.symm.continuous.continuousAt.tendsto.comp
    (hrl.prodMk_nhds hil)
  change Tendsto (fun t => Complex.equivRealProdCLM.symm
    ((F (w+Complex.equivRealProdCLM.symm (planarWiener t b))).re,
     (F (w+Complex.equivRealProdCLM.symm (planarWiener t b))).im))
    (𝓝[<] τ) (𝓝 (Complex.equivRealProdCLM.symm (Yr b,Yi b))) at hh
  simpa only [Complex.equivRealProdCLM_symm_apply,Complex.re_add_im] using hh

end SLEExactGauge

end

end OAI
