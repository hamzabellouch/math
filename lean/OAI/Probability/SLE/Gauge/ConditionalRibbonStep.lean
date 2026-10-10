import OAI.Probability.SLE.Gauge.UniformRibbonStep
import OAI.Probability.SLE.Gauge.RandomPassageBounds

namespace OAI

/-! The actual uniform ribbon step integrates against the measurable
stopped restart law. The estimate holds on every event in the past where
an actual admissible ribbon history has been certified. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw Target

local instance conditionalRibbonPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance conditionalRibbonPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance conditionalRibbonDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance conditionalRibbonDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma ribbon_section_restart_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : Ω → C(ℝ≥0, ℂ)) (hp : Measurable p)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → C(ℝ≥0, ℂ)) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, ℂ) mΩ (borel _) Y (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0, ℂ) mΩ (borel _) p P)
    (Fb : Ω → C(closedHalfPlane, ℂ)) (hFb : Measurable[m] Fb)
    {C L : ℝ≥0} {ε : ℝ} (κ v c q : ℝ)
    (S : Set C(ℝ≥0, ℂ)) (hS : MeasurableSet S)
    (E : Set Ω)
    (hstates : ∀ᵐ ω ∂P, ω ∈ E → ∃ d : RibbonHistory C L ε,
      (∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
        Fb ω z = d.inverse d.time ((d.U d.time : ℂ) + z)) ∧ d.stepEvent κ v c = S)
    (hstep : ∀ (d : RibbonHistory C L ε) (f : C(closedHalfPlane, ℂ)),
      (∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
        f z = d.inverse d.time ((d.U d.time : ℂ) + z)) →
      ENNReal.ofReal q ≤ P {ω | finiteBoundaryPath f (p ω) ∈ d.stepEvent κ v c})
    (A : Set Ω) (hA : MeasurableSet[m] A) (hAE : A ⊆ E) :
    ENNReal.ofReal q * P A ≤ P (A ∩ {ω | finiteBoundaryPath (Fb ω) (Y ω) ∈ S}) := by
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure (P.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  let T : Set (Ω × C(ℝ≥0, ℂ)) := {x | finiteBoundaryPath (Fb x.1) x.2 ∈ S}
  have hT : @MeasurableSet (Ω × C(ℝ≥0, ℂ)) (m.prod (borel _)) T := by
    let : MeasurableSpace Ω := m
    exact hS.preimage (measurable_random_finiteBoundaryPath Fb hFb)
  have hsections : ∀ᵐ ω ∂P, ω ∈ E →
      ENNReal.ofReal q ≤ P.map p {x | (ω, x) ∈ T} := by
    filter_upwards [hstates] with ω hω hωE
    obtain ⟨d, hf, he⟩ := hω hωE
    have hsec : MeasurableSet {x | finiteBoundaryPath (Fb ω) x ∈ S} :=
      hS.preimage (measurable_finiteBoundaryPath (Fb ω))
    rw [show {x | (ω, x) ∈ T} = {x | finiteBoundaryPath (Fb ω) x ∈ S} from rfl,
      Measure.map_apply hp hsec]
    change ENNReal.ofReal q ≤ P {ω' | finiteBoundaryPath (Fb ω) (p ω') ∈ S}
    simpa only [he] using hstep d (Fb ω) hf
  exact restart_event_lower_bound P (P.map p) m hm Y hY hlaw T hT E
    (ENNReal.ofReal q) hsections A hA hAE

/-- The genuine Brownian restart and the actual uniform passage estimate
give the adapted lower bound needed by concatenation. Histories are
required only on the event where the preceding steps succeeded. -/
theorem uniform_conditional_actual_ribbon_step
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (C L : ℝ≥0) (hC : 0 < C) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ (v : ℝ), 0 < v → v < v₀ → ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0))),
      ∀ (S : Set C(ℝ≥0, ℂ)), MeasurableSet S → ∀ E : Set Ω,
      (∀ᵐ ω ∂P, ω ∈ E → ∃ d : RibbonHistory C L ε,
        d.U = (fun t => Real.sqrt κ * B t ω) ∧ d.trace = γ ω ∧
        d.forward = G ω ∧ d.inverse = F ω ∧ d.time = τ ω ∧ d.stepEvent κ v c = S) →
      ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A → A ⊆ E →
        ENNReal.ofReal q * P A ≤ P (A ∩ {ω |
          (⟨fun t => γ ω (τ ω + t), (hw ω).1.comp (continuous_const.add continuous_id)⟩ :
            C(ℝ≥0, ℂ)) ∈ S}) := by
  obtain ⟨q, c, v₀, hq, hcm, hv₀, hstep⟩ :=
    uniform_actual_ribbon_step P κ hκ hκ8 B hB hm hc γ G F hw hcompact hboundary
      hsupport hplanar hstraight hexit hwiener W hW C L hC hL ε hε hεsmall
  refine ⟨q, c, v₀, hq, hcm, hv₀, ?_⟩
  intro v hv hvcut τ hτ S hS E hstates A hA hAE
  obtain ⟨Φ, Fb, hΦm, hΦ, hFbm, hFb, _, hlaw, hactual⟩ :=
    source_measurable_finite_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw hboundary τ hτ
  let p := sourceTracePath γ (fun ω => (hw ω).1)
  have hp : Measurable p := by
    have he : p = fun ω => Φ (sourceDriverPath B hc ω) := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable (sourceDriverPath B hc) hm)
  let Y := fun ω => Φ (sourceRestartDriverPath B hc τ ω)
  have hY : Measurable Y := hΦm.comp
    (source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ))))
  have hcert : ∀ᵐ ω ∂P, ω ∈ E → ∃ d : RibbonHistory C L ε,
      (∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
        Fb ω z = d.inverse d.time ((d.U d.time : ℂ) + z)) ∧ d.stepEvent κ v c = S := by
    filter_upwards [hstates] with ω hω hωE
    obtain ⟨d, hU, _, _, hF, ht, he⟩ := hω hωE
    refine ⟨d, ?_, he⟩
    intro z hz
    rw [hU, hF, ht, hFb ω z hz]
    congr 1
    simp only [Complex.ofReal_mul, add_comm]
  have hh := ribbon_section_restart_lower_bound P p hp hτ.measurableSpace
    hτ.measurableSpace_le Y hY hlaw Fb hFbm κ v c q S hS E hcert
    (fun d f hf => hstep d f hf v hv hvcut) A hA hAE
  apply hh.trans
  apply measure_mono_ae
  filter_upwards [hactual] with ω hω hωA
  refine ⟨hωA.1, ?_⟩
  have he : (⟨fun t => γ ω (τ ω + t),
      (hw ω).1.comp (continuous_const.add continuous_id)⟩ : C(ℝ≥0, ℂ)) =
      finiteBoundaryPath (Fb ω) (Y ω) := by
    ext t
    exact hω t
  change (⟨fun t => γ ω (τ ω + t),
    (hw ω).1.comp (continuous_const.add continuous_id)⟩ : C(ℝ≥0, ℂ)) ∈ S
  rw [he]
  exact hωA.2

end SLEExactGauge

end

end OAI
