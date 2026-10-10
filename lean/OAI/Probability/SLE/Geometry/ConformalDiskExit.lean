import OAI.Probability.SLE.Geometry.HolomorphicExitLimit

namespace OAI

/-! At a finite physical exit the limit of a conformal disk chart is on
the unit circle. Only continuity of the inverse inside the disk is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma disk_exit_limit_norm {D : Set ℂ} {F H : ℂ → ℂ}
    (hF : MapsTo F D (ball 0 1)) (hH : ContinuousOn H (ball 0 1))
    (hHD : MapsTo H (ball 0 1) D) (hinv : ∀ z∈D, H (F z)=z)
    (ζ : ℝ≥0 → ℂ) (hζ : Continuous ζ) (τ : ℝ≥0) (hτ : 0 < τ)
    (hpath : ∀ t<τ, ζ t∈D) (hexit : ζ τ∉D) (c : ℂ)
    (hc : Tendsto (fun t => F (ζ t)) (𝓝[<] τ) (𝓝 c)) : ‖c‖=1 := by
  let : NeBot (𝓝[<] τ) := nhdsLT_neBot_of_exists_lt ⟨0,hτ⟩
  have hmem : ∀ᶠ t in 𝓝[<] τ, ζ t∈D :=
    (show ∀ᶠ t in 𝓝[<] τ, t<τ from self_mem_nhdsWithin).mono hpath
  have hle : ‖c‖ ≤ 1 := le_of_tendsto hc.norm (hmem.mono fun t ht =>
    (mem_ball_zero_iff.mp (hF ht)).le)
  apply le_antisymm hle
  apply not_lt.mp
  intro hlt
  have hcb : c∈ball (0:ℂ) 1 := mem_ball_zero_iff.mpr hlt
  have hHlim := ((hH c hcb).continuousAt (isOpen_ball.mem_nhds hcb)).tendsto.comp hc
  have hsame : Tendsto ζ (𝓝[<] τ) (𝓝 (H c)) :=
    hHlim.congr' (hmem.mono fun t ht => hinv (ζ t) ht)
  have hid : H c=ζ τ := tendsto_nhds_unique hsame
    (hζ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  exact hexit (hid ▸ hHD hcb)

theorem conformal_disk_finite_exit_limit
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) (hw : w∈D) {F H : ℂ → ℂ}
    (hFhol : DifferentiableOn ℂ F D) (hF : MapsTo F D (ball 0 1))
    (hH : ContinuousOn H (ball 0 1)) (hHD : MapsTo H (ball 0 1) D)
    (hinv : ∀ z∈D, H (F z)=z) (T : ℝ≥0) :
    ∀ᵐ b ∂W.prod W, ∀ τ : ℝ≥0, 0 < τ → τ ≤ T →
      (∀ t<τ, w+Complex.equivRealProdCLM.symm (planarWiener t b)∈D) →
      w+Complex.equivRealProdCLM.symm (planarWiener τ b)∉D →
      ∃ c : ℂ, ‖c‖=1 ∧
        Tendsto (fun t => F (w+Complex.equivRealProdCLM.symm (planarWiener t b)))
          (𝓝[<] τ) (𝓝 c) := by
  have hb := holomorphic_domain_exit_limit W hW hD w hw hFhol T 1
    (fun z hz => (mem_ball_zero_iff.mp (hF hz)).le)
  filter_upwards [hb] with b hb
  intro τ hτ hτT hp hx
  obtain ⟨c,hc⟩ := hb τ hτT hp hx
  refine ⟨c,?_,hc⟩
  exact disk_exit_limit_norm hF hH hHD hinv _
    (continuous_const.add (Complex.equivRealProdCLM.symm.continuous.comp (planarWiener_continuous b)))
    τ hτ hp hx c hc

end SLEExactGauge

end

end OAI
