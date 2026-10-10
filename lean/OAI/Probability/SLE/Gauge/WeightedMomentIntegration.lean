import OAI.Probability.SLE.Multipoint.MultipointMomentIntegration

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

lemma lintegral_weighted_mass_pow_eq
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SigmaFinite P] [SigmaFinite μ]
    (W : Ω → X → ℝ≥0∞) (hW : Measurable (Function.uncurry W))
    (f : X → ℝ≥0∞) (hf : Measurable f) (m : ℕ) :
    (∫⁻ ω, (∫⁻ z, f z * W ω z ∂μ)^m ∂P) =
      ∫⁻ z : Fin m → X, (∏ i, f (z i)) * (∫⁻ ω, ∏ i, W ω (z i) ∂P)
        ∂Measure.pi (fun _ : Fin m => μ) := by
  rw [lintegral_mass_pow_eq P μ (fun ω z => f z * W ω z)
    ((hf.comp measurable_snd).mul hW) m]
  apply lintegral_congr
  intro z
  have hg : Measurable (fun ω => ∏ i, W ω (z i)) :=
    Finset.measurable_prod _ (fun i _ => hW.comp (measurable_id.prodMk measurable_const))
  simp_rw [Finset.prod_mul_distrib]
  exact lintegral_const_mul _ hg

end SLEExactGauge.Multipoint

end

end OAI
