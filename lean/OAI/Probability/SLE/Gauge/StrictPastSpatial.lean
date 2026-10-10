import OAI.Probability.SLE.Gauge.StrictPastExpectation
import OAI.Probability.SLE.Geometry.GreenCompactDecay

namespace OAI

/-! Spatial Green-integral versions of the strict past-mass identities. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
  (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))

include C hB hc h0 hκ hκ8 F hw

lemma strict_past_mass_spatial (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E)
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω in E, C.rational.terminal ω
      (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}) ∂P)=
      ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K, ∫⁻ ω in E,
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ*B s ω) (γ ω) (G ω) t z) ∂P ∂volume := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [C.strict_past_mass_kernel hB hc h0 hκ hκ8 F hw t E hE K hK]
  rw [← Measure.bind_apply hK.measurableSet
    (halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t).aemeasurable]
  exact halfPlaneGreenMeasure_mean_apply (P.restrict E) hBm hc κ γ G F hw t K hK.measurableSet

lemma finite_strict_past_spatial (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω, C.rational.terminal ω (K ∩ ⋃ t∈I,
      if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅) ∂P)=
      ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
        ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t,
          ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ*B s ω) (γ ω) (G ω) t z) ∂P ∂volume := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [C.finite_strict_past_expectation hB hc h0 hκ hκ8 F hw I E hE K hK]
  have hswap (t : ℝ≥0) :
      (∫⁻ ω in firstPastSuccess I E t, halfPlaneGreenMeasure κ B γ G t ω K ∂P)=
        ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K, ∫⁻ ω in firstPastSuccess I E t,
          ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ*B s ω) (γ ω) (G ω) t z) ∂P ∂volume := by
    rw [← Measure.bind_apply hK.measurableSet
      (halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t).aemeasurable]
    exact halfPlaneGreenMeasure_mean_apply (P.restrict _) hBm hc κ γ G F hw t K hK.measurableSet
  simp_rw [hswap]
  symm
  apply lintegral_finsetSum
  intro t _
  exact (actual_greenDensity_joint_measurable hBm hc κ γ G F hw t).ennreal_ofReal.lintegral_prod_left'

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
