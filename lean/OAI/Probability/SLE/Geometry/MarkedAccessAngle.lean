import OAI.Probability.SLE.Geometry.ActualMarkedStraightening
import OAI.Probability.SLE.Mass.MarkedTubeHarmonicMeasure
import OAI.Probability.SLE.Geometry.MarkedSurvivingBall
import OAI.Probability.SLE.Geometry.MarkedWindowEarly
import OAI.Probability.SLE.Geometry.NormalizedLoewnerCharts

namespace OAI

/-! The marked-point angle follows from the actual complete access guide,
two uniformly supported Brownian routes and the cited conformal exit law.
This isolates explicit physical geometry for the serpentine application. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates CrosscutSides Target

theorem uniform_marked_access_angle
    (hopen : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hsupport : PublishedPlanarWienerUnitSupport) (W : WienerLaw) (hW : IsWiener W)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F → Continuous U →
      ∀ T : ℝ≥0, 0 < T →
      (∀ S : ℝ≥0, S < T → γ T ∈ survivingDomain γ S) →
      ∀ w : ℂ, ‖w‖ ≤ 1 → 2 * a < w.im →
      (∀ q ∈ γ '' Icc 0 T, q.im ≤ w.im - 2 * a ∨ w.re + 2 * a ≤ q.re) →
      ∀ α : ℝ≥0 → ℂ, Continuous α → Function.Injective α → α 0 = γ T →
      (∀ u : ℝ≥0, 0 < u → α u ∈ survivingDomain γ T) →
      Tendsto α atTop (cocompact ℂ) →
      (∀ z ∈ ball (0 : ℂ) (a / 12),
        (∃ u : ℝ≥0, 0 < u ∧ α u = markedCornerChart w z) ↔ z.im = 0) →
      (∀ (right : Bool) (t : ℝ), t ∈ Icc (1 / 64 : ℝ) 3 → ∀ u : ℝ≥0, 0 < u →
        a / 1000 ≤ dist (markedWindowRoute right w a t) (α u)) →
      s₀ ≤ (G T w - (U T : ℂ)).im / ‖G T w - (U T : ℂ)‖ := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨q, hq, hprob⟩ := uniform_marked_window_tube_probability hsupport W hW ha ha1
  have hqfin : q ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top _ _)
    (hprob false 0 (by simp))
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqfin
  refine ⟨2 * q.toReal, by positivity, ?_⟩
  intro U γ G F hw hU T hT hfresh w hwn hwa hpast α hα hiα hα0 hαD hescape hlocus hclear
  have hQD := marked_corner_ball_survives γ T w ha hwa hpast
  obtain ⟨h, hreal, _, hzero, hloc, hloci, hlocz⟩ := actual_marked_access_straightening
    hstraight hw hU T hT hfresh α hα hiα hα0 hαD hescape (markedCornerChart w) (a / 12) hQD hlocus
  let g := fun z => G T z - (U T : ℂ)
  let f := fun z => F T ((U T : ℂ) + z)
  have hcharts := normalized_capacity_charts hw T 1 (by norm_num)
  have hgeq : normalizedForward (G T) (U T) 1 = g := by funext z; simp [normalizedForward, g]
  have hfeq : normalizedInverse (F T) (U T) 1 = f := by funext z; simp [normalizedInverse, f]
  rw [hgeq, hfeq] at hcharts
  obtain ⟨hf, _, hg, _, hfD, hgH, hgf, hfg⟩ := hcharts
  have hwD : w ∈ survivingDomain γ T := marked_ball_survives γ T w ha hwa hpast (mem_ball_self ha)
  have hgeom (right : Bool) (b : Driver × Driver)
      (hb : ∀ t ∈ Icc (0 : ℝ) 3,
        dist (physicalUnitBrownianPath w b t) (markedWindowRoute right w a t) < a / 10000) :
      ∃ τ : ℝ, UnitWindowFirstExit (survivingDomain γ T) (physicalUnitBrownianPath w b) τ ∧
        (1 / 64 : ℝ) < τ ∧ ∀ t ∈ Ico (1 / 64 : ℝ) τ,
          (h (g (physicalUnitBrownianPath w b t))).re ≠ 0 := by
    apply marked_tube_first_exit_geometry _ (isOpen_survivingDomain hw.1 T) g h α
      (fun z hz he => (hzero z hz).mp he) _ (physicalUnitBrownianPath_continuous w b)
    · intro t ht
      apply marked_ball_survives γ T w ha hwa hpast
      have hn := hb t ⟨ht.1, ht.2.trans (by norm_num)⟩
      have hd := (dist_triangle (physicalUnitBrownianPath w b t)
        (markedWindowRoute right w a t) w).trans_lt
        (add_lt_add_of_lt_of_le hn (markedWindowRoute_early_dist right w ha.le ht))
      change dist _ w < a
      linarith
    · intro hz
      have hn := hb 3 (by norm_num)
      have hi := (Complex.abs_im_le_norm
        (physicalUnitBrownianPath w b 3 - markedWindowRoute right w a 3)).trans_lt
        (show ‖physicalUnitBrownianPath w b 3 - markedWindowRoute right w a 3‖ < a / 10000 by
          simpa only [dist_eq_norm] using hn)
      rw [Complex.sub_im, markedWindowRoute_final] at hi
      have him : 0 < (physicalUnitBrownianPath w b 3).im := hz.1.1
      linarith [(abs_lt.mp hi).2]
    · intro t ht u hu he
      have hn := hb t ⟨by linarith [ht.1], ht.2⟩
      rw [he, dist_comm] at hn
      have hc := hclear right t ht u hu
      linarith
  obtain ⟨hl, hr⟩ := marked_tubes_harmonic_bounds hopen hexit W hW _
    (isOpen_survivingDomain hw.1 T) (fun z hz => hz.1.1) g f hg hf hgH hfD hfg hgf w hwD ha
    h hreal hloc hloci hlocz q (fun right => hprob right w hwn) hgeom
  exact (positive_angle_of_two_exit_probability_bounds hq (hgH hwD) hl hr).2

end SLEExactGauge.Serpentine

end

end OAI
