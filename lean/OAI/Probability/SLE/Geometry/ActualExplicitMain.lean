import OAI.Probability.SLE.Gauge.ActualDenseCoverProbability
import OAI.Probability.SLE.Gauge.DenseCoverExpectation
import OAI.Probability.SLE.Geometry.SpatialExhaustion

namespace OAI

/-! The explicit-gauge main theorem for a regular Brownian-driven Loewner
presentation, conditional on the precise published inputs used in the
geometric and stochastic construction. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance actualMainDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualMainDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma compact_upperHalfPlane_height_lower_bound {K : Set ℂ}
    (hK : IsCompact K) (hH : K ⊆ upperHalfPlane) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, η ≤ z.im := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    exact ⟨z.im, hH hz, hmin⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro z hz
    exact False.elim (hne ⟨z, hz⟩)

theorem regular_driver_gauge_mainConclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    MainConclusion P h γ := by
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγm, B, hB, Eventually.of_forall (fun ω => ⟨G ω, F ω, hw ω⟩)⟩
  obtain ⟨T, b, c, hT, hb, hcpos, v, hv, _, hprob⟩ :=
    uniform_actual_dense_cover_probability P κ hκ hκ8 B hB hBm hc hB0 γ G F hγm hw
      htrace hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
  obtain ⟨C, _, hbound⟩ := expected_hausdorff_of_dense_candidates P κ hκ hκ8 γ hSLE
    (fun ω => (hw ω).1) hT hb hcpos h hh hf
  apply mainConclusion_of_uniform_compact_interior_bounds P κ hκ hκ8 γ hSLE h hh hf
  intro R hR
  refine ⟨(C : ℝ≥0∞) * wholeSausageChargeBound κ (R + 3), ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.coe_lt_top (wholeSausageChargeBound_lt_top κ _ hκ hκ8)
  · intro t K hK hKR
    obtain ⟨η, hη, hheight⟩ := compact_upperHalfPlane_height_lower_bound hK
      (fun z hz => (hKR hz).1)
    obtain ⟨D, hD, hmiss⟩ := hprob η hη
    have hwhole := hbound R hR.le K (fun z hz => (hKR hz).2) v hv D hD.le
      (by simpa only [denseMissedProbabilityBound] using hmiss R K (fun z hz => (hKR hz).2) hheight)
    refine (lintegral_mono fun ω => measure_mono ?_).trans hwhole
    intro z hz
    exact ⟨hz.1, image_subset_range (γ ω) (Icc 0 t) hz.2⟩

/-- The regular-driver form of the explicit exact-gauge result. The same
conclusion includes finite expected measure in every bounded disk. -/
theorem regular_driver_explicit_mainConclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) :
    MainConclusion P (explicitGauge κ) γ :=
  regular_driver_gauge_mainConclusion P κ hκ hκ8 B hB hBm hc hB0 γ G F hγm hw
    htrace hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
    (explicitGauge κ) (explicitGauge_isGauge hκ) (explicitGauge_small_formula κ)

end SLEExactGauge

end

end OAI
