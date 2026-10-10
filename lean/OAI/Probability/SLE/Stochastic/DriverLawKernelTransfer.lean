import OAI.Probability.SLE.Geometry.RestartContinuationKernel
import OAI.Probability.SLE.Loewner.ScaleTraceLaw

namespace OAI

/-! A deterministic-time kernel specified by the original Brownian past
transfers to another Brownian realization with the same continuous path law. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance driverLawKernelMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance driverLawKernelBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B B' : ℝ≥0 → Ω → ℝ}

lemma source_driver_integral_of_same_law_kernel
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hc' : ∀ ω, Continuous (fun t => B' t ω))
    (hlaw : P.map (sourceDriverPath B hc)=P.map (sourceDriverPath B' hc'))
    (t : ℝ≥0) (f K : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hK : Measurable[driverPathFiltration t] K)
    (hmean : ∀ A : Set Ω,
      MeasurableSet[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] A →
      (∫⁻ ω in A, f (sourceDriverPath B hc ω) ∂P)=
        ∫⁻ ω in A, K (sourceDriverPath B hc ω) ∂P)
    (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B' (fun s => (hm' s).stronglyMeasurable)) t] E) :
    (∫⁻ ω in E, f (sourceDriverPath B' hc' ω) ∂P)=
      ∫⁻ ω in E, K (sourceDriverPath B' hc' ω) ∂P := by
  have hs := driverContinuationMean_eq_of_past_integrals hB hm hc t f K hf hK hmean
  have hKm := hK.mono (driverPathFiltration.le t) le_rfl
  have hsec : MeasurableSet {p | driverContinuationMean (P.map (sourceDriverPath B' hc'))
      t f p=K p} := measurableSet_eq_fun
    ((driverContinuationMean_measurable _ t f hf).mono (driverPathFiltration.le t) le_rfl) hKm
  rw [hlaw] at hs
  have hp := (ae_map_iff (source_path_measurable (sourceDriverPath B' hc') hm').aemeasurable hsec).mp hs
  have he := (source_driver_continuation_condLExp hB' hm' hc' t f hf).symm.trans hp
  calc
    _ = ∫⁻ ω in E, P⁻[(fun ω => f (sourceDriverPath B' hc' ω)) |
        (Filtration.natural B' (fun s => (hm' s).stronglyMeasurable)) t] ω ∂P :=
      (setLIntegral_condLExp (Filtration.le _ t) P _ hE).symm
    _ = _ := lintegral_congr_ae (ae_restrict_of_ae he)

lemma source_driver_bind_of_same_law_kernel
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hc' : ∀ ω, Continuous (fun t => B' t ω))
    (hlaw : P.map (sourceDriverPath B hc)=P.map (sourceDriverPath B' hc'))
    (t : ℝ≥0) (N K : C(ℝ≥0,ℝ) → Measure upperHalfPlane) (hN : Measurable N)
    (hK : Measurable[driverPathFiltration t] K)
    (hmean : ∀ A : Set Ω,
      MeasurableSet[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] A →
      (P.restrict A).bind (fun ω => N (sourceDriverPath B hc ω))=
        (P.restrict A).bind (fun ω => K (sourceDriverPath B hc ω)))
    (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B' (fun s => (hm' s).stronglyMeasurable)) t] E) :
    (P.restrict E).bind (fun ω => N (sourceDriverPath B' hc' ω))=
      (P.restrict E).bind (fun ω => K (sourceDriverPath B' hc' ω)) := by
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hp' : Measurable (sourceDriverPath B' hc') := source_path_measurable _ hm'
  have hKm := hK.mono (driverPathFiltration.le t) le_rfl
  have hNB : Measurable (fun ω => N (sourceDriverPath B hc ω)) := hN.comp hp
  have hKB : Measurable (fun ω => K (sourceDriverPath B hc ω)) := hKm.comp hp
  have hNB' : Measurable (fun ω => N (sourceDriverPath B' hc' ω)) := hN.comp hp'
  have hKB' : Measurable (fun ω => K (sourceDriverPath B' hc' ω)) := hKm.comp hp'
  apply Measure.ext
  intro S hS
  rw [Measure.bind_apply hS hNB'.aemeasurable,
    Measure.bind_apply hS hKB'.aemeasurable]
  apply source_driver_integral_of_same_law_kernel hB hB' hm hm' hc hc' hlaw t
    (fun p => N p S) (fun p => K p S)
    ((Measure.measurable_coe hS).comp hN) ((Measure.measurable_coe hS).comp hK) ?_ E hE
  intro A hA
  have he := congrArg (fun μ : Measure upperHalfPlane => μ S) (hmean A hA)
  simpa only [Measure.bind_apply hS hNB.aemeasurable,
    Measure.bind_apply hS hKB.aemeasurable] using he

end SLEExactGauge

end

end OAI
