import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableCoordinates

namespace OAI

/-! # Returning the complex averaged limit to real spacetime -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem spacetime_average_limit (r : ℕ → KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (hi : ∀ n, Integrable (fourierSource (r n) ψ))
    (q : Lp ℂ 1 (volume : Measure FourierSpace))
    (hc : ∀ K : Set FourierSpace, volume K < ⊤ →
      Tendsto (fun n => eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-
        (q : FourierSpace → ℂ)) 1 (volume.restrict K)) atTop (𝓝 0)) :
    LocalL1Converges (fun n => resolventAverage (r n) ψ)
      (fun z => (q (spacetimeHilbertEquiv z)).re) := by
  have hq : Integrable (fun z => q (spacetimeHilbertEquiv z)) :=
    spacetimeHilbert_measurePreserving.integrable_comp_of_integrable (L1.integrable_coeFn q)
  refine ⟨hq.re.locallyIntegrable,fun K hK => ?_⟩
  let S := spacetimeHilbertEquiv '' K
  have hS : volume S < ⊤ := by
    have he := spacetimeHilbert_measurePreserving.measure_preimage_emb
      spacetimeHilbertEquiv.measurableEmbedding S
    rw [show spacetimeHilbertEquiv ⁻¹' S = K from
      preimage_image_eq _ spacetimeHilbertEquiv.injective] at he
    exact he ▸ hK.measure_lt_top
  have he n : eLpNorm (fun z => velocityLineAverage (fourierSource (r n) ψ)
      (spacetimeHilbertEquiv z)-q (spacetimeHilbertEquiv z)) 1 (volume.restrict K) =
      eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ))
        1 (volume.restrict S) :=
    by
      simpa only [Function.comp_def,Pi.sub_apply,S] using
        eLpNorm_comp_equiv_restrict spacetimeHilbertEquiv spacetimeHilbert_measurePreserving
          (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ)) K
  have hb n : eLpNorm (fun z => resolventAverage (r n) ψ z-(q (spacetimeHilbertEquiv z)).re)
      1 (volume.restrict K) ≤
      eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ))
        1 (volume.restrict S) := by
    rw [← he n]
    have hav := spacetimeHilbert_measurePreserving.integrable_comp_of_integrable
      (velocityLineAverage_integrable (hi n))
    have hm : AEStronglyMeasurable (fun z => (velocityLineAverage (fourierSource (r n) ψ)
        (spacetimeHilbertEquiv z)-q (spacetimeHilbertEquiv z)).re) (volume.restrict K) :=
      (hav.sub hq).aestronglyMeasurable.re.restrict
    apply eLpNorm_mono (by
      convert hm using 1
      ext z
      simp only [Complex.sub_re,fourierSource_average,Complex.ofReal_re])
    intro z
    rw [fourierSource_average]
    simpa only [Complex.sub_re,Complex.ofReal_re,Real.norm_eq_abs] using
      Complex.abs_re_le_norm ((resolventAverage (r n) ψ z : ℂ)-q (spacetimeHilbertEquiv z))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hc S hS)
    (fun _ => bot_le) hb

end BoltzmannNonuniqueness.Published

end

end OAI
