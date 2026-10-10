import OAI.Probability.SLE.Geometry.ActualExplicitMain

namespace OAI

/-! Passage from a regular presentation to an arbitrary ordinary SLE.
The subtype restriction preserves the published geometric support input,
and whole-trace expectations transfer through its measure-preserving map. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance explicitTransferDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance explicitTransferDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- The same continuous Brownian path, retaining its pointwise zero start. -/
def sourceBasedDriverPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0)
    (ω : Ω) : Driver where
  toContinuousMap := sourceDriverPath B hc ω
  map_zero' := h0 ω

lemma sourceBasedDriverPath_measurable
    {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0) :
    Measurable (sourceBasedDriverPath B hc h0) := by
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  exact source_path_measurable _ hm

/-- An ordinary regular presentation supplies the based Wiener law needed
by the two-dimensional Brownian support input. -/
theorem sourceBasedDriverLaw_isWiener
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0) :
    IsWiener (P.map (sourceBasedDriverPath B hc h0)) := by
  have hbp := sourceBasedDriverPath_measurable B hm hc h0
  refine ⟨⟨fun I => ?_⟩, Eventually.of_forall (fun b => map_continuous b)⟩
  have hI : Measurable (fun b : Driver => I.restrict (fun t => b t)) :=
    Measurable.of_eval (fun i => (continuous_eval_const (i : ℝ≥0)).measurable)
  refine ⟨hI.aemeasurable, ?_⟩
  rw [Measure.map_map hI hbp]
  exact (hB.hasLaw I).map_eq

theorem RegularSLEPresentation.geometric_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hsupport : PublishedGeometricTubeSupport P γ) :
    PublishedGeometricTubeSupport (P.comap (Subtype.val : a.samples → Ω))
      (fun ω => γ ω) := by
  intro z p hp hpH N V hN hV hpN hzV
  let E : Set Ω := {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) N ∧ γ ω T ∈ V}
  have hemb : MeasurableEmbedding (Subtype.val : a.samples → Ω) :=
    MeasurableEmbedding.subtype_coe a.measurable_samples
  have he : (P.comap (Subtype.val : a.samples → Ω))
      ((Subtype.val : a.samples → Ω) ⁻¹' E) = P E := by
    rw [← hemb.map_apply, a.measurePreserving_val.map_eq]
  change 0 < (P.comap (Subtype.val : a.samples → Ω))
    ((Subtype.val : a.samples → Ω) ⁻¹' E)
  rw [he]
  exact hsupport z p hp hpH N V hN hV hpN hzV

theorem ordinary_explicit_main_of_regular_presentation
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (a : RegularSLEPresentation P κ γ)
    (htrace : PublishedTraceGeneration
      ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
      κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) :
    MainConclusion P (explicitGauge κ) γ := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  let : IsProbabilityMeasure Q := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  have hmain := regular_driver_explicit_mainConclusion Q κ hκ hκ8 a.B a.brownian hBm
    a.continuous_B a.zero_B (fun ω => γ ω) a.G a.F
    (fun t => (hSLE.1 t).comp measurable_subtype_coe) a.witness htrace
    hcompact hboundary (a.geometric_support hsupport) hplanar hstraight hexit hwiener W hW
  apply (mainConclusion_iff_finiteExpectedWholeTrace P κ hκ hκ8 γ hSLE
    (explicitGauge κ) (explicitGauge_isGauge hκ) (explicitGauge_small_formula κ)).mpr
  intro R hR
  have hb := finiteExpectedWholeTrace_of_mainConclusion Q (explicitGauge κ)
    (fun ω => γ ω) hmain R hR
  have hemb : MeasurableEmbedding (Subtype.val : a.samples → Ω) :=
    MeasurableEmbedding.subtype_coe a.measurable_samples
  have he := a.measurePreserving_val.lintegral_comp_emb hemb
    (fun ω => hausdorffGauge (explicitGauge κ) (wholeTrace (γ ω) ∩ closedBall 0 R))
  exact he.symm.trans_lt hb

/-- A fixed choice is used only to state the precise canonical-driver law
on which the Rohde--Schramm trace-generation input is needed. -/
def ordinaryRegularPresentation
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) :
    RegularSLEPresentation P κ γ := Classical.choice (exists_regular_sle_presentation hSLE)

def ordinaryRegularDriverLaw
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) : Measure C(ℝ≥0, ℝ) :=
  let a := ordinaryRegularPresentation hSLE
  (P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B)

/-- The explicit exact-gauge main conclusion for any ordinary chordal SLE,
conditional on the same eight published inputs as the regular theorem. -/
theorem ordinary_explicit_mainConclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (htrace : PublishedTraceGeneration (ordinaryRegularDriverLaw hSLE) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) :
    MainConclusion P (explicitGauge κ) γ :=
  ordinary_explicit_main_of_regular_presentation P κ hκ hκ8 γ hSLE
    (ordinaryRegularPresentation hSLE) htrace hcompact hboundary hsupport hplanar hstraight
    hexit hwiener W hW

/-- The final ordinary-SLE theorem has no auxiliary Wiener-law assumption:
that law is constructed from the chosen regular Brownian presentation. -/
theorem ordinary_explicit_mainConclusion_of_published_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (htrace : PublishedTraceGeneration (ordinaryRegularDriverLaw hSLE) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport) :
    MainConclusion P (explicitGauge κ) γ := by
  let a := ordinaryRegularPresentation hSLE
  let W : WienerLaw := (P.comap (Subtype.val : a.samples → Ω)).map
    (sourceBasedDriverPath a.B a.continuous_B a.zero_B)
  have hW : IsWiener W := sourceBasedDriverLaw_isWiener a.B a.brownian
    a.measurable_B a.continuous_B a.zero_B
  exact ordinary_explicit_mainConclusion P κ hκ hκ8 γ hSLE htrace hcompact hboundary
    hsupport hplanar hstraight hexit hwiener W hW

end SLEExactGauge

end

end OAI
