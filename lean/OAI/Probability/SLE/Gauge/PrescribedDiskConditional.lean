import OAI.Probability.SLE.Gauge.PrescribedDiskTestKernel
import OAI.Probability.SLE.Geometry.PastDensityIntegral

namespace OAI

/-! The normalized disk success probability is a genuine conditional lower
bound under the actual finite centered law, tested against its full past. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance diskConditionalMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance diskConditionalBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_disk_conditional_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.of_uncurry_left : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u v r b : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hr : 0 < r)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (hlive : ∀ ω∈E, z ∈ survivingDomain (γ ω) (τ ω))
    (hbase : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
    (hR : ∀ ω∈E, fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r) :
    ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
      (∫⁻ ω in A∩E, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (stoppedMarkedCenter κ B γ G τ z ω).arg
        ∂finiteCenteredLaw P κ B γ G z (u+v)) ≤
      finiteCenteredLaw P κ B γ G z (u+v)
        (A∩E∩C.prescribedBallTest (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v))
          z ((4096*Real.pi)*r)
          (ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*ENNReal.ofReal b)) := by
  obtain ⟨M,hM,_hMf,hMp,hbound⟩ := C.prescribed_disk_test_kernel hB hc h0 hκ hκ8
    F hw R he D hD hDf hDp hgrowth hpublished τ hτ z hz u v r b hu hv hr E hE hlive hbase hR
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  have hq : Measurable[hτ.measurableSpace] (fun ω =>
      R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v
        (stoppedMarkedCenter κ B γ G τ z ω).arg) := by
    let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
      (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
    exact (R.angleDiskTail_measurable _ κ b v).comp
      (source_stoppedMarkedCenter_measurable B hm hc κ γ G F hw τ hτ z).carg
  intro A hA
  rw [← past_density_test_integral P (finiteCenteredLaw P κ B γ G z (u+v))
    hτ.measurableSpace hτ.measurableSpace_le M hM E hE hMp _ hq A hA]
  exact hbound A hA

end SLEExactGauge.Multipoint

end

end OAI
