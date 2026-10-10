import OAI.Probability.SLE.Mass.DilationMass
import OAI.Probability.SLE.Mass.WeightedImageRandomMass
import OAI.Probability.SLE.Stochastic.ProgressiveParameterTime

namespace OAI

/-! Measurability of the actual mass normalization when its scale and
evaluation time are selected from the stopped past. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma dilationMass_measurable_family {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (c : Ω → ℝ≥0) (hc : Measurable c) (hpos : ∀ ω, 0<c ω)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) :
    Measurable (fun ω => dilationMass κ (c ω) (hpos ω) (μ ω)) := by
  let J : Ω × upperHalfPlane → upperHalfPlane := fun p => halfPlaneDilation (c p.1) (hpos p.1) p.2
  have hJ : Measurable J := by
    apply Measurable.subtype_mk
    exact (Complex.measurable_ofReal.comp
      (NNReal.continuous_coe.measurable.comp (hc.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)
  let w : Ω × upperHalfPlane → ℝ≥0∞ := fun p => ENNReal.ofReal ((c p.1:ℝ)^dimension κ)
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    ((NNReal.continuous_coe.measurable.comp (hc.comp measurable_fst)).pow measurable_const)
  exact weightedImageMass_measurable μ hμ hfin J hJ w hw

end SLEExactGauge.Multipoint

end

end OAI
