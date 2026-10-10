import OAI.Probability.SLE.Gauge.PrescribedAngleMain
import OAI.Probability.SLE.Geometry.ActualExplicitTransfer

namespace OAI

/-! Transfer of the exact prescribed-gauge criterion from a regular
Brownian presentation to the original ordinary SLE probability space. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedTransferMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance prescribedTransferBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem RegularSLEPresentation.prescribed_main_of_canonical_angle_bounds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0<κ) (hκ8 : κ<8) (hγ : ∀ t, Measurable (fun ω => γ ω t))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (htrace : PublishedTraceGeneration
      ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
      κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi,
      (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
        canonicalAngleAverage
          ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
          κ v f θ ∧
      canonicalAngleAverage
          ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
          κ v f θ ≤ 2*(∫⁻ φ, f φ ∂Target.angleLaw κ)) :
    MainConclusion P (Target.gauge κ W) γ := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  let : IsProbabilityMeasure Q := a.probability
  have hBm : Measurable (Function.uncurry a.B) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨C⟩ := Multipoint.exists_canonicalMass a.brownian hBm a.continuous_B a.zero_B
    hκ hκ8 (fun ω => γ ω) a.G a.F a.witness hgrowth
  have hmain := C.prescribed_main_of_canonical_angle_bounds a.brownian a.continuous_B
    a.zero_B hκ hκ8 a.F a.witness (fun t => (hγ t).comp measurable_subtype_coe)
    hgrowth htrace W hW δ hδ hangle
  have hemb : MeasurableEmbedding (Subtype.val : a.samples → Ω) :=
    MeasurableEmbedding.subtype_coe a.measurable_samples
  constructor
  · rw [← a.measurePreserving_val.map_eq,hemb.ae_map_iff]
    exact hmain.1
  · intro L hL
    obtain ⟨hm,M,hM⟩ := hmain.2 L hL
    refine ⟨(a.measurePreserving_val.aemeasurable_comp_iff hemb).mp hm,M,?_⟩
    have he := a.measurePreserving_val.lintegral_comp_emb hemb
      (fun ω => hausdorffGauge (Target.gauge κ W) (wholeTrace (γ ω)∩Metric.closedBall 0 L))
    rw [← he]
    exact hM

theorem ordinary_prescribed_main_of_canonical_angle_bounds
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (htrace : PublishedTraceGeneration (ordinaryRegularDriverLaw hSLE) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi,
      (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
          canonicalAngleAverage (ordinaryRegularDriverLaw hSLE) κ v f θ ∧
      canonicalAngleAverage (ordinaryRegularDriverLaw hSLE) κ v f θ ≤
          2*(∫⁻ φ, f φ ∂Target.angleLaw κ)) :
    MainConclusion P (Target.gauge κ W) γ :=
  (ordinaryRegularPresentation hSLE).prescribed_main_of_canonical_angle_bounds
    hκ hκ8 hSLE.1 hgrowth htrace W hW δ hδ hangle

end SLEExactGauge

end

end OAI
