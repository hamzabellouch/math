import OAI.Probability.SLE.Geometry.ActualWaypointStraightening
import OAI.Probability.SLE.Mass.WaypointHarmonicMeasure
import OAI.Probability.SLE.Geometry.NormalizedLoewnerCharts

namespace OAI

/-! The actual uniform ribbon waypoint angle.  Uniform Brownian route
support, crosscut topology, and conformal Brownian exit bounds are the
published inputs.  The positive ribbon angle is derived here. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates
open Target CrosscutSides

theorem uniform_actual_ribbon_waypoint_angle
    (hopen : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hsupport : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (C K : ℝ≥0) (hK : 0 < (K : ℝ)) :
    ∃ s : ℝ, 0 < s ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F → Continuous U →
      ∀ (P : ℂ → ℂ), ContinuousOn P closedRibbon → InjOn P closedRibbon →
      (∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane) →
      Tendsto (fun t : ℝ => ‖P (t : ℂ)‖) atTop atTop →
      ∀ (k ε x : ℝ), 1 ≤ k → 0 < ε → ε ≤ 1 / 8 → |x| ≤ 1 / 16 →
      LipschitzOnWith C P (crossingPatch k) →
      (∀ u ∈ crossingPatch k, ∀ v ∈ crossingPatch k,
        dist u v ≤ K * dist (P u) (P v)) →
      ∀ (xp : ℝ≥0 → ℂ) (T : ℝ≥0), 0 < T → ContinuousOn xp (Icc 0 T) →
      EqOn γ (P ∘ xp) (Icc 0 T) → (xp 0).re = 0 →
      xp T = (k : ℂ) + (x : ℂ) * Complex.I →
      MapsTo xp (Icc 0 T) closedRibbon →
      (∀ t ∈ Icc 0 T, (xp t).re ≤ k ∧ |(xp t).im| ≤ ε) →
      (∀ t : ℝ≥0, t < T → (xp t).re < k) →
      s ≤ (G T (P ((k + 1 / 2 : ℝ) : ℂ)) - (U T : ℂ)).im /
        ‖G T (P ((k + 1 / 2 : ℝ) : ℂ)) - (U T : ℂ)‖ := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨q, hq, hprob⟩ := uniform_physical_waypoint_tube_probability
    hsupport W hW C (div_pos (by norm_num : (0 : ℝ) < 1 / 32) hK)
  have hqfin : q ≠ ⊤ := by
    have hb := hprob (fun _ => (0 : ℂ)) 1 1 (by norm_num)
      ((LipschitzWith.const (0 : ℂ)).weaken (show (0 : ℝ≥0) ≤ C from bot_le)).lipschitzOnWith
    exact ne_top_of_le_ne_top (measure_ne_top _ _) hb
  have hqreal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqfin
  refine ⟨2 * q.toReal, by positivity, ?_⟩
  intro U γ G F hw hU P hP hiP hH hescape k ε x hk hε hεsmall hx hupper hlower
    xp T hT hxp hγ hxp0 htip hcoords hcore hfront
  have htipre : (xp T).re = k := by simp [htip]
  have htipim : (xp T).im = x := by simp [htip]
  have hxquarter : |x| ≤ 1 / 4 := hx.trans (by norm_num)
  have hfresh := ribbon_front_tip_survives_prior P hP hiP hH hescape γ xp T hxp hxp0
    hcoords hγ (fun t ht => by rw [htipre]; exact hfront t ht)
    (by rw [htipim]; exact hx.trans_lt (by norm_num))
  have hpast : γ '' Icc 0 T ⊆ P '' {z ∈ closedRibbon | z.re ≤ k} := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨xp t, ⟨hcoords ht, (hcore t ht).1⟩, (hγ ht).symm⟩
  have hunbounded := futureRibbon_unbounded_of_centerline_escape P k hescape
  have hfuture : P '' futureRibbon k ⊆ survivingDomain γ T :=
    futureRibbon_survives P hP hiP (by linarith) hH γ T hpast hunbounded
  have hphysicalTip : P ((k : ℂ) + (x : ℂ) * Complex.I) = γ T := by
    rw [← htip]
    exact (hγ ⟨bot_le, le_rfl⟩).symm
  obtain ⟨h, hreal, _, hcut, hloc, hloci, hlocz⟩ :=
    actual_ribbon_waypoint_straightening hstraight hw hU T hT hfresh P hP hiP
      (by linarith) hxquarter hphysicalTip hfuture hescape
  let g := fun z => G T z - (U T : ℂ)
  let f := fun z => F T ((U T : ℂ) + z)
  have hcharts := normalized_capacity_charts hw T 1 (by norm_num)
  have hgeq : normalizedForward (G T) (U T) 1 = g := by
    funext z
    simp [normalizedForward, g]
  have hfeq : normalizedInverse (F T) (U T) 1 = f := by
    funext z
    simp [normalizedInverse, f]
  rw [hgeq, hfeq] at hcharts
  obtain ⟨hf, _, hg, _, hfD, hgH, hgf, hfg⟩ := hcharts
  obtain ⟨hl, hr⟩ := ribbon_tube_harmonic_bounds hopen hexit W hW K hK P hP hiP hH
    hk hε hεsmall hx hlower γ xp hw.1 T hT hxp hγ hxp0 htipre hcoords hcore hunbounded
    g f hg hf hgH hfD hfg hgf h hreal hcut hloc hloci hlocz q
    (fun side hs => hprob P k side (by rcases hs with rfl | rfl <;> norm_num) hupper)
  have hwD : P ((k + 1 / 2 : ℝ) : ℂ) ∈ survivingDomain γ T := by
    apply hfuture
    exact ⟨((k + 1 / 2 : ℝ) : ℂ), ⟨by simp, by simp⟩, rfl⟩
  exact (positive_angle_of_two_exit_probability_bounds hq (hgH hwD) hl hr).2

end SLEExactGauge.RibbonCoordinates

end

end OAI
