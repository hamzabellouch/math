import OAI.Probability.SLE.Gauge.ActualDenseExtended
import OAI.Probability.SLE.Angle.ActualAngleWarmupExtended
import OAI.Probability.SLE.Geometry.ExtendedMarkedAngle
import OAI.Probability.SLE.Geometry.FiniteCenteredConsistency

namespace OAI

/-! The complete conditional dense test: one unit of angle warmup followed
by the dense experiment, under any common later finite centered law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance conditionalDenseDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance conditionalDenseDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance conditionalDensePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance conditionalDensePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem uniform_actual_conditional_dense_test
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
    ∃ h b C : ℝ, 0 < h ∧ h ≤ 1 / 2 ∧ 0 < b ∧ 0 < C ∧
      ∃ δ : ℕ → ℝ, (∀ N, 0 < N → 0 < δ N) ∧
      ∀ (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u),
        ∀ N : ℕ, 0 < N → ∀ v : ℝ, 0 < v →
          v < δ N * ((2 * z.im) * Real.exp (-(u + 1))) →
          ∀ V : ℝ, u + 1 + Serpentine.experimentRadiusLevel h ≤ V →
          ∀ A : Set Ω, MeasurableSet[(actual_radiusLevelTime_stopping hB
            (fun _t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hc hB0
            κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A →
            ENNReal.ofReal ((1 / 2) * Real.exp (-C * (N : ℝ) ^ 2)) *
              finiteCenteredLaw P κ B γ G z V A ≤
            finiteCenteredLaw P κ B γ G z V
              (A ∩ stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
                (fun ω => radiusLevelTime (γ ω) (G ω) z (u + 1 + Serpentine.experimentRadiusLevel h))
                (closedBall z ((2 * z.im) * Real.exp (-(u + 1))))
                (b * ((2 * z.im) * Real.exp (-(u + 1))) ^ dimension κ * (N : ℝ) ^ codimension κ)) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨Φ, Gc, Fc, _, hWc⟩ := exists_measurable_canonical_witness
    (P.map (sourceDriverPath B hc)) κ htrace
  obtain ⟨s, hs, hs1, hwarm⟩ :=
    actual_radius_angle_warmup P κ hκ hκ8 B hB hBm hc hB0 γ G F hw Φ Gc Fc hWc
  obtain ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, hdense⟩ :=
    uniform_actual_dense_at_extended_good_radius_state P κ hκ hκ8 B hB hBm hc hB0 γ G F
      hγm hw htrace hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW hs hs1
  have hhalf : h ≤ 1 / 2 := by linarith
  have hq : 0 ≤ Serpentine.experimentRadiusLevel h :=
    Serpentine.experimentRadiusLevel_nonneg hh (by linarith)
  refine ⟨h, b, C, hh, hhalf, hb, hC, δ, hδ, ?_⟩
  intro z hz u hu N hN v hv hvcut V hV A hA
  let U := u + 1 + Serpentine.experimentRadiusLevel h
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hu1 : 0 ≤ u + 1 := by linarith
  let E : Set Ω := {ω | canonicalRadiusLevel κ (u + 1, z, sourceDriverPath B hc ω) < ∞ ∧
    s ≤ canonicalStoppedSine κ (u + 1, z, sourceDriverPath B hc ω)}
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z (u + 1)
  have hσ := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz (u + 1) hu1
  have hE : MeasurableSet[hσ.measurableSpace] E :=
    canonical_good_angle_measurable_at_radius hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz (u + 1) s hu1
  have hA1 : MeasurableSet[hσ.measurableSpace] A :=
    (actual_radiusLevelTime_past_mono hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u (u + 1)
      hu (by linarith)) A hA
  have hEext (ω : Ω) (hω : ω ∈ E) :
      ω ∈ extendedMarkedGood κ B γ G σ z s := by
    rwa [← canonical_good_angle_eq_extendedMarkedGood κ B hc γ G F hw z (u + 1) s hu1]
  have hbase (ω : Ω) (hω : ω ∈ E) :
      fullRadius (G ω) ((σ ω).untopD 0) z = (2 * z.im) * Real.exp (-(u + 1)) := by
    exact (actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z (u + 1) (hEext ω hω).1).2
  let S := stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
    (fun ω => radiusLevelTime (γ ω) (G ω) z U)
    (closedBall z ((2 * z.im) * Real.exp (-(u + 1))))
    (b * ((2 * z.im) * Real.exp (-(u + 1))) ^ dimension κ * (N : ℝ) ^ codimension κ)
  have hd := hdense σ hσ z hz (u + 1) hu1 E hE (fun ω hω => (hEext ω hω).1)
    (fun ω hω => (hEext ω hω).2) hbase N hN v hv hvcut A hA1
  have hσU := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz U hU
  have hpast := actual_radiusLevelTime_past_mono hB hm hBm hc hB0 κ hκ hκ8 γ G F hw
    z hz (u + 1) U hu1 (by dsimp [U]; linarith)
  have hAU : MeasurableSet[hσU.measurableSpace] A := hpast A hA1
  have hEU : MeasurableSet[hσU.measurableSpace] E := hpast E hE
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => γ ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω) _ _ γ G F hw
    · intro t
      exact measurable_const.mul
        ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
    · intro ω
      exact (hc ω).const_mul _
  have hS : MeasurableSet[hσU.measurableSpace] S :=
    stoppedMassTest_measurable_at_stop _ γ hγa (fun ω => (hw ω).1) _ hσU κ v _ _
  have hcons (D : Set Ω) (hD : MeasurableSet[hσU.measurableSpace] D) :
      finiteCenteredLaw P κ B γ G z V D = finiteCenteredLaw P κ B γ G z U D :=
    finiteCenteredLaw_consistent_at_radius_stop hB hBm hc hB0 κ hκ hκ8 γ G F
      (Eventually.of_forall hw) z hz U V hU hV _ hσU Filter.EventuallyEq.rfl D hD
  have hd' : ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) *
      finiteCenteredLaw P κ B γ G z V (A ∩ E) ≤ finiteCenteredLaw P κ B γ G z V (A ∩ S) := by
    rw [hcons _ (hAU.inter hEU), hcons _ (hAU.inter hS)]
    exact hd.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))
  have hwarm' := hwarm z hz u hu V (by linarith) A hA
  calc
    _ = ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) *
        (ENNReal.ofReal (1 / 2 : ℝ) * finiteCenteredLaw P κ B γ G z V A) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.exp (-C * (N : ℝ) ^ 2)) *
        finiteCenteredLaw P κ B γ G z V (A ∩ E) := mul_le_mul' le_rfl hwarm'
    _ ≤ _ := hd'

end SLEExactGauge

end

end OAI
