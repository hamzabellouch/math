import OAI.Probability.SLE.Gauge.RibbonStepTranslation

namespace OAI

/-! Uniform one-step probability in the original physical ribbon, for any
actual continuous boundary realization of the stopped inverse map. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw RibbonPassageScaling Target

local instance uniformStepPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance uniformStepPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def translateFiniteBoundary (a : ℂ) (f : C(closedHalfPlane, ℂ)) :
    C(closedHalfPlane, ℂ) := ⟨fun z => a + f z, continuous_const.add f.continuous⟩

lemma finiteBoundaryPath_translate (a : ℂ) (f : C(closedHalfPlane, ℂ))
    (p : C(ℝ≥0, ℂ)) (t : ℝ≥0) :
    finiteBoundaryPath (translateFiniteBoundary a f) p t =
      affine a 1 (finiteBoundaryPath f p t) := by
  simp only [finiteBoundaryPath, translateFiniteBoundary, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, affine, Complex.ofReal_one, one_mul]

def RibbonHistory.stepEvent {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (κ v c : ℝ) : Set C(ℝ≥0, ℂ) :=
  frontMassEvent (longitudinalCoordinate d.chart closedRibbon d.front)
    (physicalPassageRegion d.stepChart ribbonStepCompact C ε (ε / L))
    (d.chart ((d.front : ℂ) + 1)) (ε / L) κ v c
    (physicalMiddleRegion d.chart closedRibbon d.front ε)

lemma RibbonHistory.finiteBoundary_step_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) (hε : ε ≤ 1 / 8)
    (f : C(closedHalfPlane, ℂ)) (p : Ω → C(ℝ≥0, ℂ))
    (κ v c : ℝ) (hv : 0 < v) :
    P {ω | finiteBoundaryPath (translateFiniteBoundary (d.trace d.time) f) (p ω) ∈
        d.stepEvent κ v c} =
      P {ω | finiteBoundaryPath f (p ω) ∈
        frontMassEvent (longitudinalCoordinate d.recenteredChart ribbonStepCompact 0)
          (physicalPassageRegion d.recenteredChart ribbonStepCompact C ε (ε / L))
          (d.recenteredChart 1) (ε / L) κ v c
          (physicalMiddleRegion d.recenteredChart ribbonStepCompact 0 ε)} := by
  have hη (ω : Ω) : (finiteBoundaryPath
      (translateFiniteBoundary (d.trace d.time) f) (p ω) : ℝ≥0 → ℂ) =
      fun t => affine (d.trace d.time) 1 (finiteBoundaryPath f (p ω) t) := by
    funext t
    exact finiteBoundaryPath_translate _ _ _ _
  have hh := d.frontMass_probability_translate P hε
    (fun ω => (finiteBoundaryPath f (p ω) : ℝ≥0 → ℂ)) κ v c hv
  simpa only [RibbonHistory.stepEvent, frontMassEvent, hη, finiteBoundaryPath_translate,
    PassageSuccess.FrontSuccess, mem_ofPred_eq] using hh

lemma RibbonHistory.step_lower {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) :
    ∀ u ∈ ribbonStepCompact, ∀ v ∈ ribbonStepCompact,
      dist u v ≤ L * dist (d.stepChart u) (d.stepChart v) := by
  intro u hu v hv
  simpa only [RibbonHistory.stepChart, dist_add_left] using
    d.patch_lower _ (translate_ribbonStepCompact hu) _ (translate_ribbonStepCompact hv)

lemma RibbonHistory.stepChart_continuousOn {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) : ContinuousOn d.stepChart ribbonStepCompact :=
  d.chart_continuous.comp (continuous_const.add continuous_id).continuousOn d.stepCompact_maps

lemma RibbonHistory.global_progress_eq_step {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) :
    EqOn (longitudinalCoordinate d.chart closedRibbon d.front)
      (longitudinalCoordinate d.stepChart ribbonStepCompact 0)
      (d.stepChart '' ribbonStepCompact) := by
  have hi := lower_lipschitz_injOn d.stepChart ribbonStepCompact L d.step_lower
  rintro z ⟨w, hw, rfl⟩
  simp only [longitudinalCoordinate, RibbonHistory.stepChart,
    coordinateInverse_left d.chart_injective (d.stepCompact_maps hw), Complex.add_re,
    Complex.ofReal_re, add_sub_cancel_left, sub_zero]
  exact congrArg Complex.re (coordinateInverse_left hi hw).symm

lemma RibbonHistory.stepEvent_measurable {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (hplanar : PublishedPlanarDiskOpenness)
    (hε : ε ≤ 1 / 8) (κ v c : ℝ) : MeasurableSet (d.stepEvent κ v c) := by
  have hK := ribbonStepCompact_isCompact.image_of_continuousOn d.stepChart_continuousOn
  have hp : ContinuousOn (longitudinalCoordinate d.chart closedRibbon d.front)
      (d.stepChart '' ribbonStepCompact) :=
    (longitudinalCoordinate_continuousOn d.stepChart ribbonStepCompact L 0 d.step_lower).congr
      (fun z hz => d.global_progress_eq_step hz)
  have hV : IsOpen (physicalPassageRegion d.stepChart ribbonStepCompact C ε (ε / L)) := by
    have he : ribbonStepCompact ∩ passageCoordinateRegion C ε (ε / L) =
        interior ribbonStepCompact ∩ passageCoordinateRegion C ε (ε / L) := by
      apply Subset.antisymm
      · exact fun z hz => ⟨ribbonStepCompact_passage hε C (ε / L) hz, hz.2⟩
      · exact inter_subset_inter_left _ interior_subset
    unfold physicalPassageRegion
    rw [he]
    exact isOpen_image_coordinate_subset hplanar d.stepChart ribbonStepCompact _
      d.stepChart_continuousOn (lower_lipschitz_injOn _ _ L d.step_lower)
      (isOpen_interior.inter (passageCoordinateRegion_isOpen C ε (ε / L)))
      (inter_subset_left.trans interior_subset)
  exact measurableSet_frontMassEvent _ _ _ _ κ v c _ _ hK.isClosed hp hV
    (image_mono inter_subset_left)

/-- This is the uniform one-step estimate for an actual stopped history.
The boundary chart can be the already past-measurable chart used in its
restart law; no measurable selection of compactness outputs is required. -/
theorem uniform_actual_ribbon_step
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous (fun t => B t ω))
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
      ∀ (d : RibbonHistory C L ε) (Fb : C(closedHalfPlane, ℂ)),
        (∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
          Fb z = d.inverse d.time ((d.U d.time : ℂ) + z)) →
        ∀ v : ℝ, 0 < v → v < v₀ →
          ENNReal.ofReal q ≤ P {ω |
            finiteBoundaryPath Fb (sourceTracePath γ (fun ω => (hw ω).1) ω) ∈
              d.stepEvent κ v c} := by
  obtain ⟨Fc, hFc, q, c, v₀, hq, hc, hv₀, hprob⟩ :=
    uniform_actual_ribbon_passage P κ hκ hκ8 B hB hm hcont γ G F hw
      hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW C L hC hL
      ε hε hεsmall
  refine ⟨q, c, v₀, hq, hc, hv₀, ?_⟩
  intro d Fb hFb v hv hvcut
  have he : Fb = translateFiniteBoundary (d.trace d.time) (Fc d) := by
    apply finite_boundary_ext
    intro z hz
    change Fb z = d.trace d.time + Fc d z
    rw [hFb z hz, hFc d z hz]
    abel
  rw [he, d.finiteBoundary_step_probability P hεsmall (Fc d)
    (sourceTracePath γ (fun ω => (hw ω).1)) κ v c hv]
  exact hprob d v hv hvcut

end SLEExactGauge

end

end OAI
