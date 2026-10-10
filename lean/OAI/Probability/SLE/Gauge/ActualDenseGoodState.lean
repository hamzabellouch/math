import OAI.Probability.SLE.Gauge.ActualDenseIntegration
import OAI.Probability.SLE.Geometry.FiniteDensityAtRadiusState
import OAI.Probability.SLE.Geometry.StoppedMarkedStateMeasurability
import OAI.Probability.SLE.Geometry.FixedCanonicalRestart

namespace OAI

/-! The dense experiment at an actual finite stopping time, conditional on
its live good-angle radius state. Constants are chosen before the stopping
time, marked point and stopped-past event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FrontSuccessMeasurability
open Target

local instance actualGoodDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualGoodDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualGoodPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance actualGoodPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma measurable_actual_radius_level
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) :
    Measurable (fun ω => radiusLevelTime (γ ω) (G ω) z u) := by
  have hbp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hk : Measurable (fun ω => canonicalRadiusLevel κ (u, z, sourceDriverPath B hc ω)) :=
    measurable_canonicalRadiusLevel_random_state κ hbp measurable_const measurable_const
  have he : (fun ω => canonicalRadiusLevel κ (u, z, sourceDriverPath B hc ω)) =
      (fun ω => radiusLevelTime (γ ω) (G ω) z u) :=
    funext (fun ω => canonicalRadiusLevel_eq κ (sourceDriverPath B hc ω) (hw ω) u hu z)
  rwa [he] at hk

lemma measurable_actual_stopped_mass_test
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hγm : ∀ t, Measurable (fun ω => γ ω t))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (v r b : ℝ) :
    MeasurableSet (stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
      (fun ω => radiusLevelTime (γ ω) (G ω) z u) (closedBall z r) b) := by
  have hlevel := measurable_actual_radius_level κ B hm hc γ G F hw z u hu
  have hpath : Measurable (sourceTracePath γ (fun ω => (hw ω).1)) :=
    source_path_measurable _ hγm
  exact measurableSet_le measurable_const ((wholeSausageCharge_measurable κ v _).comp
    (measurable_stoppedAtPath _ hpath _ hlevel))

theorem uniform_actual_dense_at_good_radius_state
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
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ h b C : ℝ, 0 < h ∧ h ≤ s / 2 ∧ 0 < b ∧ 0 < C ∧
      ∃ δ : ℕ → ℝ, (∀ N, 0 < N → 0 < δ N) ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτ : IsStoppingTime (Filtration.natural B
          (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
          (fun ω => (τ ω : WithTop ℝ≥0)))
        (z : ℂ), z ∈ upperHalfPlane → ∀ u : ℝ, 0 ≤ u →
        ∀ E : Set Ω, MeasurableSet[hτ.measurableSpace] E →
          E ⊆ stoppedMarkedGood κ B γ G τ z s →
          (∀ ω ∈ E, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u)) →
          ∀ N : ℕ, 0 < N → ∀ v : ℝ, 0 < v →
            v < δ N * ((2 * z.im) * Real.exp (-u)) →
            ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
              ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) *
                finiteCenteredLaw P κ B γ G z (u + Serpentine.experimentRadiusLevel h) (A ∩ E) ≤
              finiteCenteredLaw P κ B γ G z (u + Serpentine.experimentRadiusLevel h)
                (A ∩ stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
                  (fun ω => radiusLevelTime (γ ω) (G ω) z (u + Serpentine.experimentRadiusLevel h))
                  (closedBall z ((2 * z.im) * Real.exp (-u)))
                  (b * ((2 * z.im) * Real.exp (-u)) ^ dimension κ * (N : ℝ) ^ codimension κ)) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨Φ, Gc, Fc, hΦ, hΦW, hΦγ⟩ :=
    canonical_witness_original_trace P κ B hm hc γ G F hw htrace
  obtain ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, hsections⟩ :=
    Serpentine.uniform_canonical_conformal_dense_sections P κ hκ hκ8 B hB hBm hc hB0 γ G F hw
      Φ hΦ hΦγ hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
      (1 / 16) (by norm_num) (by norm_num) hs hs1
  refine ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, ?_⟩
  intro τ hτ z hz u hu E hE hgood hbase N hN v hv hvcut A hA
  let a := stoppedMarkedScale κ B γ G τ z
  let w := stoppedMarkedUnit κ B γ G τ z
  let Y := normalizedRestartDriverPath B hc τ a
  let q := Serpentine.experimentRadiusLevel h
  have hq : 0 < q := by
    dsimp [q, Serpentine.experimentRadiusLevel]
    have hlog : Real.log (h / 80) < 0 := Real.log_neg (by positivity) (by linarith)
    linarith
  have ham : Measurable[hτ.measurableSpace] a :=
    source_stoppedMarkedScale_measurable B hm hc κ γ G F hw τ hτ z
  have ha : ∀ ω, 0 < a ω := stoppedMarkedScale_pos κ B γ G τ z
  have hwm : Measurable[hτ.measurableSpace] w :=
    source_stoppedMarkedUnit_measurable B hm hc κ γ G F hw τ hτ z
  obtain ⟨Fb, hFb, hYm, _, hFbEq, _, hYlaw, hrestart⟩ :=
    source_normalized_restart_with_factor κ hκ hκ8 B hB hm hc γ G F hw Φ hΦ Gc Fc hΦW
      hboundary τ hτ a ham ha
  have hlive (ω : Ω) (hω : ω ∈ E) : z ∈ survivingDomain (γ ω) (τ ω) :=
    (hgood hω).1
  have hgeometry (ω : Ω) (hω : ω ∈ E) :=
    source_stoppedMarkedState_geometry B hc κ γ G F hw τ z ω (hlive ω hω)
  have hpoint (ω : Ω) (hω : ω ∈ E) :
      F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ)) = z := by
    simpa only [normalizedInverse, add_comm] using (hgeometry ω hω).2.2.1
  have hcanonical (ω : Ω) (hω : ω ∈ E) :
      ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) ≤
      ((P.map (sourceDriverPath B hc)).withDensity
        (fun p => canonicalFiniteDensity κ (q, w ω, p)))
        (canonicalDenseEvent κ Φ (Fb ω) q (w ω) b
          ((2 * z.im) * Real.exp (-u)) N v z) := by
    let f := normalizedInverse (F ω (τ ω)) (Real.sqrt κ * B (τ ω) ω) (a ω : ℝ)
    have hgeo := hgeometry ω hω
    have hchart (ζ : closedHalfPlane) (hζ : (ζ : ℂ) ∈ upperHalfPlane) : Fb ω ζ = f ζ := by
      simpa only [f, normalizedInverse, add_comm] using hFbEq ω ζ hζ
    have hrad : 2 * (w ω).im * ‖deriv f (w ω)‖ = (2 * z.im) * Real.exp (-u) :=
      hgeo.2.2.2.2.2.2.trans (hbase ω hω)
    have hv' : v < δ N * (2 * (w ω).im * ‖deriv f (w ω)‖) := by rwa [hrad]
    have hh := hsections f (Fb ω) (w ω) hgeo.2.2.2.1 hgeo.2.2.2.2.1 hchart
      hgeo.1 (hgood hω).2 hgeo.2.2.2.2.2.1 N hN v hv hv'
    have hfw : f (w ω) = z := hgeo.2.2.1
    simpa only [q, hfw, hrad] using hh
  obtain ⟨M, hM, hMfinite, hMactual, hMpast⟩ :=
    exists_finiteDensity_at_radius_state hB hBm hc hB0 κ hκ hκ8 γ G F hw
      τ hτ z hz u q hu hq E hE hlive hbase
  have hS : MeasurableSet (stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
      (fun ω => radiusLevelTime (γ ω) (G ω) z (u + q))
      (closedBall z ((2 * z.im) * Real.exp (-u)))
      (b * ((2 * z.im) * Real.exp (-u)) ^ dimension κ * (N : ℝ) ^ codimension κ)) :=
    measurable_actual_stopped_mass_test κ B hm hc γ G F hγm hw z (u + q) (by linarith) v _ _
  have h := actual_dense_sections_integrate P (P.map (sourceDriverPath B hc))
    hτ.measurableSpace hτ.measurableSpace_le κ B hc γ G F hw Y hYm hYlaw Φ hΦ Fb hFb
    τ a ha (fun ω => Gc (Y ω)) (fun ω => Fc (Y ω))
    (hrestart.mono (fun _ hω => hω.1))
    (fun ω => normalizedRestartDriverPath_driver κ B hc τ a ω)
    (hrestart.mono (fun _ hω t => (hω.2 t).symm)) w hwm E hE
    (fun ω hω => (hgeometry ω hω).2.1) z u q b ((2 * z.im) * Real.exp (-u)) v hq.le N
    hpoint hbase M hM hMfinite hMactual
    (ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2))) ENNReal.ofReal_ne_top hcanonical hS A hA
  rw [hMpast A hA] at h
  exact h

end SLEExactGauge

end

end OAI
