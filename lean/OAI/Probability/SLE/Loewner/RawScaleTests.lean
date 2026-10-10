import OAI.Probability.SLE.Mass.RandomDilationMass
import OAI.Probability.SLE.Mass.CanonicalMassScaling

namespace OAI

/-! Fixed-scale covariance of the same raw functional, expressed as
measurable scalar tests on continuous driver space. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance rawScaleTestsMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawScaleTestsBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma RawCanonicalMass.scaled_parameter_measurable {Ω : Type*} [MeasurableSpace Ω]
    (R : RawCanonicalMass) (c T : Ω → ℝ≥0) (hc : Measurable c) (hT : Measurable T)
    (Y : Ω → C(ℝ≥0,ℝ)) (hY : Measurable Y) :
    Measurable (fun ω => R.process ((c ω)^2*T ω) (scaleDriverPath (c ω) (Y ω))) :=
  _root_.OAI.MeasureTheory.IsProgressive.parameter_time_measurable R.progressive
    (fun ω => scaleDriverPath (c ω) (Y ω))
    (measurable_scaleDriverPath.comp (hc.prodMk hY))
    (fun ω => (c ω)^2*T ω) ((hc.pow_const 2).mul hT)

lemma CanonicalMass.raw_scaled_test_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (c : ℝ≥0) (hpos : 0<c) (t : ℝ≥0)
    (f : upperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    ∀ᵐ p ∂P.map (sourceDriverPath B hc),
      (∫⁻ z, f z ∂dilationMass κ c hpos (R.process t p)) =
        ∫⁻ z, f z ∂(R.process (c^2*t) (scaleDriverPath c p)) := by
  have hm (s) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hleft : Measurable (fun p => ∫⁻ z, f z ∂dilationMass κ c hpos (R.process t p)) :=
    (Measure.measurable_lintegral hf).comp
      ((conformalMass_measurable _ _).comp (R.progressive.adapted.measurable (i:=t)))
  have hright : Measurable (fun p => ∫⁻ z, f z ∂(R.process (c^2*t) (scaleDriverPath c p))) :=
    (Measure.measurable_lintegral hf).comp
      ((R.progressive.adapted.measurable (i:=c^2*t)).comp
        (measurable_scaleDriverPath.comp (measurable_const.prodMk measurable_id)))
  apply (ae_map_iff (source_path_measurable _ hm).aemeasurable
    (measurableSet_eq_fun hleft hright)).mpr
  filter_upwards [he,C.scaled_raw_process_eq hB hc F hw R he E hE hEf hEp c hpos] with ω heω hs
  rw [heω.1 t,hs t]
  rfl

end SLEExactGauge.Multipoint

end

end OAI
