import OAI.Probability.SLE.Gauge.UniformRecenteredPassage
import OAI.Probability.SLE.Geometry.ActualWaypointAngle
import OAI.Probability.SLE.Gauge.RibbonStepPatch

namespace OAI

/-! Uniform one-step passage for actual ribbon histories. The two-sided
waypoint angle and the compactness hypotheses are derived from the fixed
patch bounds, the actual first-front past, and the published analytic and
probabilistic inputs. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw Target

/-- Data at an actual attained ribbon front, before any restart. -/
structure RibbonHistory (C L : ℝ≥0) (ε : ℝ) where
  U : ℝ≥0 → ℝ
  trace : ℝ≥0 → ℂ
  forward : ℝ≥0 → ℂ → ℂ
  inverse : ℝ≥0 → ℂ → ℂ
  driver_continuous : Continuous U
  witness : IsCapacityTwoWitness U trace forward inverse
  chart : ℂ → ℂ
  chart_continuous : ContinuousOn chart closedRibbon
  chart_injective : InjOn chart closedRibbon
  chart_upper : ∀ z ∈ closedRibbon, 0 < z.re → chart z ∈ upperHalfPlane
  chart_escape : Tendsto (fun t : ℝ => ‖chart (t : ℂ)‖) atTop atTop
  front : ℝ
  offset : ℝ
  front_ge_one : 1 ≤ front
  offset_bound : |offset| ≤ ε / 4
  patch_upper : LipschitzOnWith C chart (ribbonStepPatch front)
  patch_lower : ∀ u ∈ ribbonStepPatch front, ∀ v ∈ ribbonStepPatch front,
    dist u v ≤ L * dist (chart u) (chart v)
  time : ℝ≥0
  time_pos : 0 < time
  coordinates : ℝ≥0 → ℂ
  coordinates_continuous : ContinuousOn coordinates (Icc 0 time)
  trace_coordinates : EqOn trace (chart ∘ coordinates) (Icc 0 time)
  initial_front : (coordinates 0).re = 0
  attained : coordinates time = (front : ℂ) + (offset : ℂ) * Complex.I
  coordinates_ribbon : MapsTo coordinates (Icc 0 time) closedRibbon
  past_core : ∀ t ∈ Icc 0 time, (coordinates t).re ≤ front ∧ |(coordinates t).im| ≤ ε
  strict_past : ∀ t : ℝ≥0, t < time → (coordinates t).re < front

def RibbonHistory.guide {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) (t : ℝ) : ℂ :=
  d.chart (guideCoordinate d.front d.offset t)

def RibbonHistory.recenteredChart {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (z : ℂ) : ℂ :=
  d.chart ((d.front : ℂ) + z) - d.trace d.time

theorem uniform_actual_ribbon_passage
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (Gbase Fbase : Ω → ℝ≥0 → ℂ → ℂ)
    (hwbase : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (Gbase ω) (Fbase ω))
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
    ∃ Fb : RibbonHistory C L ε → C(closedHalfPlane, ℂ),
      (∀ d (z : closedHalfPlane), z.1 ∈ upperHalfPlane → Fb d z =
        d.inverse d.time ((d.U d.time : ℂ) + z) - d.trace d.time) ∧
      ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
        ∀ d : RibbonHistory C L ε, ∀ v : ℝ, 0 < v → v < v₀ →
          ENNReal.ofReal q ≤ P {ω |
            finiteBoundaryPath (Fb d) (sourceTracePath γ (fun ω => (hwbase ω).1) ω) ∈
              frontMassEvent (longitudinalCoordinate d.recenteredChart ribbonStepCompact 0)
                (physicalPassageRegion d.recenteredChart ribbonStepCompact C ε (ε / L))
                (d.recenteredChart 1) (ε / L) κ v c
                (physicalMiddleRegion d.recenteredChart ribbonStepCompact 0 ε)} := by
  have hLr : 0 < (L : ℝ) := hL
  have hx (d : RibbonHistory C L ε) : |d.offset| ≤ 1 / 4 := by
    linarith [d.offset_bound]
  have hguideL (d : RibbonHistory C L ε) :
      LipschitzOnWith C d.chart (guidePatch d.front) :=
    d.patch_upper.mono (guidePatch_subset_ribbonStepPatch _)
  have hguideLower (d : RibbonHistory C L ε) :
      ∀ u ∈ guidePatch d.front, ∀ v ∈ guidePatch d.front,
        dist u v ≤ L * dist (d.chart u) (d.chart v) := by
    intro u hu v hv
    exact d.patch_lower u (guidePatch_subset_ribbonStepPatch _ hu)
      v (guidePatch_subset_ribbonStepPatch _ hv)
  have hgeom (d : RibbonHistory C L ε) := ribbon_access_guide_geometry hplanar
    d.chart d.chart_continuous d.chart_injective d.chart_upper d.chart_escape
    d.trace d.coordinates d.time d.coordinates_continuous d.initial_front
    d.coordinates_ribbon d.trace_coordinates d.front d.offset
    (by linarith [d.front_ge_one]) (hx d) d.attained d.strict_past C L hLr
    (hguideL d) (hguideLower d)
  have hpast (d : RibbonHistory C L ε) :
      d.trace '' Icc 0 d.time ⊆ d.chart '' {z ∈ closedRibbon | z.re ≤ d.front} := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨d.coordinates t, ⟨d.coordinates_ribbon ht, (d.past_core t ht).1⟩,
      (d.trace_coordinates ht).symm⟩
  have hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ (d : RibbonHistory C L ε) t, t ∈ Icc δ 2 →
        ball (d.guide t) r ⊆ survivingDomain d.trace d.time := by
    intro δ hδ _
    refine ⟨min δ 1 / (4 * L), div_pos (lt_min hδ zero_lt_one) (by positivity), ?_⟩
    intro d t ht
    apply (ball_subset_ball ?_).trans
      (physical_guide_clearance_of_patch hplanar d.chart d.chart_continuous d.chart_injective
        (by linarith [d.front_ge_one]) (hx d) hLr d.chart_upper d.trace d.time (hpast d)
        (futureRibbon_unbounded_of_centerline_escape d.chart d.front d.chart_escape)
        (hguideLower d) t ⟨hδ.trans_le ht.1, ht.2⟩)
    exact div_le_div_of_nonneg_right (min_le_min_right 1 ht.1) (by positivity)
  obtain ⟨s, hs, hangle⟩ := uniform_actual_ribbon_waypoint_angle hplanar hstraight hexit
    hwiener W hW C L hLr
  have hang (d : RibbonHistory C L ε) :
      s ≤ (d.forward d.time (d.guide (1 / 2)) - (d.U d.time : ℂ)).im /
        ‖d.forward d.time (d.guide (1 / 2)) - (d.U d.time : ℂ)‖ := by
    have hh := hangle d.U d.trace d.forward d.inverse d.witness d.driver_continuous
      d.chart d.chart_continuous d.chart_injective d.chart_upper d.chart_escape
      d.front ε d.offset d.front_ge_one hε hεsmall (by linarith [d.offset_bound])
      (d.patch_upper.mono (crossingPatch_subset_ribbonStepPatch _))
      (fun u hu v hv => d.patch_lower u (crossingPatch_subset_ribbonStepPatch _ hu)
        v (crossingPatch_subset_ribbonStepPatch _ hv))
      d.coordinates d.time d.time_pos d.coordinates_continuous d.trace_coordinates
      d.initial_front d.attained d.coordinates_ribbon d.past_core d.strict_past
    simpa only [RibbonHistory.guide, guideCoordinate_waypoint] using hh
  have hQU (d : RibbonHistory C L ε) :
      LipschitzOnWith C d.recenteredChart ribbonStepCompact := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro u hu v hv
    simpa only [RibbonHistory.recenteredChart, dist_sub_right, dist_add_left] using
      d.patch_upper.dist_le_mul _ (translate_ribbonStepCompact hu) _
        (translate_ribbonStepCompact hv)
  have hQL (d : RibbonHistory C L ε) :
      ∀ u ∈ ribbonStepCompact, ∀ v ∈ ribbonStepCompact,
        dist u v ≤ L * dist (d.recenteredChart u) (d.recenteredChart v) := by
    intro u hu v hv
    simpa only [RibbonHistory.recenteredChart, dist_sub_right, dist_add_left] using
      d.patch_lower _ (translate_ribbonStepCompact hu) _ (translate_ribbonStepCompact hv)
  have hQ0 (d : RibbonHistory C L ε) : ‖d.recenteredChart 0‖ ≤ C := by
    have htip : d.chart ((d.front : ℂ) + (d.offset : ℂ) * Complex.I) = d.trace d.time := by
      rw [← d.attained]
      exact (d.trace_coordinates ⟨bot_le, le_rfl⟩).symm
    have hmem : (d.front : ℂ) + (d.offset : ℂ) * Complex.I ∈ ribbonStepPatch d.front := by
      change d.front - 1 ≤ ((d.front : ℂ) + (d.offset : ℂ) * Complex.I).re ∧
        ((d.front : ℂ) + (d.offset : ℂ) * Complex.I).re ≤ d.front + 3 ∧
        |((d.front : ℂ) + (d.offset : ℂ) * Complex.I).im| ≤ 1
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, zero_add]
      exact ⟨by linarith, by linarith, (hx d).trans (by norm_num)⟩
    have hzero : (d.front : ℂ) ∈ ribbonStepPatch d.front := by
      change d.front - 1 ≤ d.front ∧ d.front ≤ d.front + 3 ∧ |(0 : ℝ)| ≤ 1
      constructor
      · linarith
      · constructor <;> norm_num
    have hd := d.patch_upper.dist_le_mul _ hzero _ hmem
    have hdist : dist (d.front : ℂ) ((d.front : ℂ) + (d.offset : ℂ) * Complex.I) =
        |d.offset| := by
      rw [dist_self_add_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hdist, htip, dist_eq_norm] at hd
    simpa only [RibbonHistory.recenteredChart, add_zero] using
      hd.trans (mul_le_of_le_one_right C.coe_nonneg ((hx d).trans (by norm_num)))
  apply uniform_recentered_passage_from_geometry P κ hκ hκ8 B₀ hB₀ hm hc γ Gbase Fbase
    hwbase hcompact hboundary hsupport hplanar
    RibbonHistory.U RibbonHistory.trace RibbonHistory.forward RibbonHistory.inverse
    RibbonHistory.driver_continuous RibbonHistory.witness RibbonHistory.time RibbonHistory.time_pos
    (fun d => (hgeom d).2.2.2.2.1) RibbonHistory.guide (2 * C) s (1 / L)
    (by positivity) hs (one_div_pos.mpr hLr)
    (fun d => (hgeom d).2.2.2.2.2.1) (fun d => (hgeom d).2.2.1)
    (fun d => (hgeom d).2.2.2.2.2.2.1) (fun d => (hgeom d).2.2.2.1)
    hclear RibbonHistory.recenteredChart ribbonStepCompact ribbonStepCompact_isCompact
    0 ribbonStepCompact_zero C L C hC hL hQU hQL hQ0 RibbonHistory.offset ε hε
    RibbonHistory.offset_bound (ribbonStepCompact_core hεsmall)
    (fun d t _ => by simp only [RibbonHistory.recenteredChart, RibbonHistory.guide,
      guideCoordinate_translate]) hang (ribbonStepCompact_passage hεsmall C (ε / L))

end SLEExactGauge

end

end OAI
