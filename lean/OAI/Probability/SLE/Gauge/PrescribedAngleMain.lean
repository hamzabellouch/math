import OAI.Probability.SLE.Gauge.PrescribedLowerAngle
import OAI.Probability.SLE.Gauge.PrescribedUpperAngle
import OAI.Probability.SLE.Mass.RawScaledMassPaths
import OAI.Probability.SLE.MainReduction

namespace OAI

/-! A uniform canonical angle estimate implies the exact prescribed-gauge
Hausdorff conclusion. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance prescribedMainMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance prescribedMainBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_main_of_canonical_angle_bounds
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hγ : ∀ t, Measurable (fun ω => γ ω t))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ v : ℝ, δ≤v → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi,
      (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
          canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ∧
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ≤
          2*(∫⁻ φ, f φ ∂Target.angleLaw κ)) :
    MainConclusion P (Target.gauge κ W) γ := by
  obtain ⟨R,he,D,hD,hDf,hDp⟩ := C.exists_raw_positive_paths hc
  have hg := C.prescribed_gauge_admissible hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW
  have hg' : IsGauge (Target.gauge κ W) := ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγ,B,hB,Eventually.of_forall (fun ω => ⟨G ω,F ω,hw ω⟩)⟩
  have hp := C.positive_prescribed_all_segments_of_canonical_angle_bound hB hc h0 hκ hκ8
    F hw R he D hD hDf hDp hgrowth hpublished W hW δ hδ
    (fun v hv f hf θ hθ => (hangle v hv f hf θ hθ).2)
  have hfinite : FiniteExpectedWholeTrace P (Target.gauge κ W) γ := by
    intro L hL
    let K : Set ℂ := closedBall 0 L ∩ {z : ℂ | 0≤z.im}
    have hK : IsClosed K := isClosed_closedBall.inter
      (isClosed_le continuous_const Complex.continuous_im)
    have hb := C.prescribed_expectation_of_canonical_angle_bound hB hc h0 hκ hκ8
      F hw R he D hD hDf hDp hgrowth hpublished W hW hγ δ hδ
      (fun v hv f hf θ hθ => (hangle v hv f hf θ hθ).1)
      L hL.le K hK inter_subset_left (fun _ h => h.2)
    have heq (ω : Ω) : range (γ ω)∩K=wholeTrace (γ ω)∩closedBall 0 L := by
      change range (γ ω)∩K=range (γ ω)∩closedBall 0 L
      ext z
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · rintro ⟨⟨t,rfl⟩,hz⟩
        exact ⟨mem_range_self t,hz,(hw ω).2.2.1 t⟩
    simpa only [Target.hausdorff_eq_hausdorffGauge,heq,Measure.toOuterMeasure_apply] using hb
  apply mainConclusion_of_lower_and_finiteExpectation P (Target.gauge κ W) γ
    (Eventually.of_forall (fun ω => (hw ω).1)) _
    (fun _ _ => source_sle_whole_trace_aemeasurable P κ γ hSLE _ hg' _ isClosed_closedBall)
    hfinite
  filter_upwards [hp] with ω hω
  intro s t _hs hst
  simpa only [Target.hausdorff_eq_hausdorffGauge,Measure.toOuterMeasure_apply,segment]
    using hω s t hst

end SLEExactGauge.Multipoint

end

end OAI
