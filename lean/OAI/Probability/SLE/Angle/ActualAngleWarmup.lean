import OAI.Probability.SLE.Loewner.CanonicalInverseAngle
import OAI.Probability.SLE.Geometry.NormalizedCanonicalRestart
import OAI.Probability.SLE.Geometry.StoppedMarkedStateMeasurability
import OAI.Probability.SLE.Geometry.FiniteDensityAtRadiusState
import OAI.Probability.SLE.Mass.RestartStoppedMass
import OAI.Probability.SLE.Geometry.RestartWeightedKernel

namespace OAI

/-! A one-unit conformal-radius warmup has a uniformly positive chance of
producing a good angle, conditionally on every actual stopped-past event.
The estimate uses the canonical Loewner witness. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance warmupDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance warmupDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance warmupPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance warmupPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma IsCapacityTwoWitness.normalized_restart_stopped_sine
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (w : ℂ) (u v : ℝ)
    (hbase : fullRadius G T (F T ((a : ℂ) * w + (U T : ℂ))) =
      (2 * (F T ((a : ℂ) * w + (U T : ℂ))).im) * Real.exp (-u))
    (hfinite : radiusLevelTime β G' w v < ∞) :
    radiusLevelTime γ G (F T ((a : ℂ) * w + (U T : ℂ))) (u + v) < ∞ ∧
    Real.sin (Complex.arg (G (radiusLevelTime γ G
        (F T ((a : ℂ) * w + (U T : ℂ))) (u + v)).toNNReal
        (F T ((a : ℂ) * w + (U T : ℂ))) -
      (U (radiusLevelTime γ G (F T ((a : ℂ) * w + (U T : ℂ)))
        (u + v)).toNNReal : ℂ))) =
      Real.sin (Complex.arg (G' (radiusLevelTime β G' w v).toNNReal w -
        (normalizedRestartDriver U T a (radiusLevelTime β G' w v).toNNReal : ℂ))) := by
  have hV : Continuous (normalizedRestartDriver U T a) := by
    unfold normalizedRestartDriver
    fun_prop
  obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hfinite
  have hs := radiusLevelTime_eq_of_live_level hV hb w v t ht hR
  have hp := (hw.normalized_restart_level_of_live_source hU T a ha hb w u v hbase t ht hR).2
  refine ⟨by rw [hp]; exact ENNReal.coe_lt_top, ?_⟩
  rw [hp, hs, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
  have hbup := normalized_restart_witness T a ha hb
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have htu : (a : ℂ) * w ∈ survivingDomain (sourceScaleTrace a β) (a ^ 2 * t) := by
    rw [source_scale_domain_iff a _ ha β, source_scale_time_mul_sq a t ha,
      mul_div_cancel_left₀ w haC]
    exact ht
  have hc := hw.restart_centered_value T hbup (a ^ 2 * t) ((a : ℂ) * w) htu
  rw [sourceScaleChart, source_scale_time_mul_sq a t ha,
    mul_div_cancel_left₀ w haC] at hc
  have hscale : (a : ℂ) * G' t w - ((U (T + a ^ 2 * t) - U T : ℝ) : ℂ) =
      (a : ℂ) * (G' t w - (normalizedRestartDriver U T a t : ℂ)) := by
    rw [normalizedRestartDriver, Complex.ofReal_div]
    field_simp
  rw [hc, hscale, sin_arg_pos_real_mul (a : ℝ) ha]

/-- The canonical measurable event is exactly the geometric stopped-angle
condition for the supplied actual witness. -/
lemma canonical_good_angle_source_eq
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (u s : ℝ) (hu : 0 ≤ u) :
    {ω | canonicalRadiusLevel κ (u, z, sourceDriverPath B hc ω) < ∞ ∧
      s ≤ canonicalStoppedSine κ (u, z, sourceDriverPath B hc ω)} =
    {ω | radiusLevelTime (γ ω) (G ω) z u < ∞ ∧
      s ≤ Real.sin (Complex.arg (G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z -
        (Real.sqrt κ * B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω : ℝ)))} := by
  ext ω
  simp only [mem_ofPred_eq, canonicalRadiusLevel_eq κ (sourceDriverPath B hc ω) (hw ω) u hu z]
  by_cases hf : radiusLevelTime (γ ω) (G ω) z u < ∞
  · rw [canonicalStoppedSine_eq κ (sourceDriverPath B hc ω) (hw ω) u hu z hf]
    rfl
  · simp only [hf, false_and]

/-- The actual finite centered law is compared on every stopped-past event.
The scale and canonical witness may be fixed before choosing that event. -/
theorem actual_one_unit_angle_warmup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hW : ∀ᵐ p ∂P.map (sourceDriverPath B hc), IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) :
    ∃ s : ℝ, 0 < s ∧ ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B
        (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)))
      (z : ℂ), z ∈ upperHalfPlane → ∀ (u : ℝ), 0 ≤ u →
      ∀ (E : Set Ω), MeasurableSet[hτ.measurableSpace] E →
      (∀ ω ∈ E, z ∈ survivingDomain (γ ω) (τ ω)) →
      (∀ ω ∈ E, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u)) →
      ∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
        ENNReal.ofReal (1 / 2 : ℝ) * finiteCenteredLaw P κ B γ G z (u + 1) (A ∩ E) ≤
          finiteCenteredLaw P κ B γ G z (u + 1)
            (A ∩ E ∩ {ω | canonicalRadiusLevel κ (u + 1, z, sourceDriverPath B hc ω) < ∞ ∧
              s ≤ canonicalStoppedSine κ (u + 1, z, sourceDriverPath B hc ω)}) := by
  classical
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let bp := sourceDriverPath B hc
  let ν := P.map bp
  have hbpm : Measurable bp := source_path_measurable _ hm
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hbpm.aemeasurable).mpr inferInstance
  obtain ⟨s, hs, hsections⟩ := canonical_uniform_good_angle ν
    (canonical_driver_isBrownian B hB hm hc) κ hκ hκ8 Φ Gc Fc hW
  refine ⟨s, hs, ?_⟩
  intro τ hτ z hz u hu E hE hlive hbase A hA
  let a := stoppedMarkedScale κ B γ G τ z
  let w := stoppedMarkedUnit κ B γ G τ z
  let Y := normalizedRestartDriverPath B hc τ a
  have ham : Measurable[hτ.measurableSpace] a :=
    source_stoppedMarkedScale_measurable B hm hc κ γ G F hw τ hτ z
  have ha : ∀ ω, 0 < a ω := stoppedMarkedScale_pos κ B γ G τ z
  have hwm : Measurable[hτ.measurableSpace] w :=
    source_stoppedMarkedUnit_measurable B hm hc κ γ G F hw τ hτ z
  have hYm : Measurable Y := by
    have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
      source_path_measurable _ (fun t => (measurable_pi_apply t).comp
        (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
    exact measurable_scaleDriverPath.comp
      ((ham.inv.mono hτ.measurableSpace_le le_rfl).prodMk hrm)
  have hYlaw (D : Set Ω) (hD : MeasurableSet[hτ.measurableSpace] D) :
      (P.restrict D).map Y = P D • ν :=
    source_restart_random_scale_driver_law B hB hm hc τ hτ
      (fun ω => (a ω)⁻¹) ham.inv (fun ω => inv_pos.mpr (ha ω)) D hD
  have hYlaw₀ : P.map Y = ν := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hYlaw univ MeasurableSet.univ
  have hYw := canonical_witness_pullback hW Y hYm hYlaw₀
  have hgeometry (ω : Ω) (hω : ω ∈ E) :=
    source_stoppedMarkedState_geometry B hc κ γ G F hw τ z ω (hlive ω hω)
  have hpoint (ω : Ω) (hω : ω ∈ E) :
      F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ)) = z := by
    simpa only [normalizedInverse, add_comm] using (hgeometry ω hω).2.2.1
  obtain ⟨M, hM, hMfinite, hMactual, hMpast⟩ :=
    exists_finiteDensity_at_radius_state hB hBm hc hB0 κ hκ hκ8 γ G F hw
      τ hτ z hz u 1 hu (by norm_num) E hE hlive hbase
  let C : Set (Ω × C(ℝ≥0, ℝ)) := {q | q.1 ∈ E ∧
    canonicalRadiusLevel κ (1, w q.1, q.2) < ∞ ∧
      s ≤ canonicalStoppedSine κ (1, w q.1, q.2)}
  let K : Ω × C(ℝ≥0, ℝ) → ℝ≥0∞ :=
    fun q => M q.1 * canonicalFiniteDensity κ (1, w q.1, q.2)
  let S : Set Ω := E ∩ {ω | canonicalRadiusLevel κ (u + 1, z, bp ω) < ∞ ∧
    s ≤ canonicalStoppedSine κ (u + 1, z, bp ω)}
  let Z : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z (u + 1) / initialGreen κ z)
  have hCm : @MeasurableSet (Ω × C(ℝ≥0, ℝ)) (hτ.measurableSpace.prod _) C :=
    (hE.preimage measurable_fst).inter
      (@measurableSet_canonical_good_angle_random_state (Ω × C(ℝ≥0, ℝ))
        (hτ.measurableSpace.prod _) κ s _ measurable_snd _ measurable_const _
        (hwm.comp measurable_fst))
  have hKm : @Measurable (Ω × C(ℝ≥0, ℝ)) ℝ≥0∞ (hτ.measurableSpace.prod _) _ K :=
    (hM.comp measurable_fst).mul ((canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk ((hwm.comp measurable_fst).prodMk measurable_snd)))
  have hSm : MeasurableSet S := (hτ.measurableSpace_le E hE).inter
    (measurableSet_canonical_good_angle_random_state κ s hbpm measurable_const measurable_const)
  have hsec : ∀ᵐ ω ∂P, ENNReal.ofReal (1 / 2 : ℝ) * E.indicator M ω ≤
      ∫⁻ p, C.indicator K (ω, p) ∂ν := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ E
    · let D : Set C(ℝ≥0, ℝ) := {p | canonicalRadiusLevel κ (1, w ω, p) < ∞ ∧
        s ≤ canonicalStoppedSine κ (1, w ω, p)}
      have hDm : MeasurableSet D := measurableSet_canonical_good_angle_random_state κ s
        measurable_id measurable_const measurable_const
      have he : (fun p => C.indicator K (ω, p)) =
          fun p => M ω * D.indicator (fun p => canonicalFiniteDensity κ (1, w ω, p)) p := by
        funext p
        by_cases hp : p ∈ D <;> simp only [C, K, D, mem_ofPred_eq] at hp ⊢ <;>
          simp [hω, hp]
      rw [he, lintegral_const_mul' _ _ (hMfinite ω), indicator_of_mem hω,
        lintegral_indicator hDm, ← withDensity_apply _ hDm]
      have hb := hsections (w ω) (hgeometry ω hω).2.1 1 (by norm_num)
      change ENNReal.ofReal (1 / 2 : ℝ) ≤
        (ν.withDensity (fun p => canonicalFiniteDensity κ (1, w ω, p))) D at hb
      calc
        _ = M ω * ENNReal.ofReal (1 / 2 : ℝ) := mul_comm _ _
        _ ≤ _ := mul_le_mul' le_rfl hb
    · simp [C, hω]
  have hactual : ∀ᵐ ω ∂P, C.indicator K (ω, Y ω) ≤ S.indicator Z ω := by
    filter_upwards [hYw, hMactual] with ω hy hMω
    by_cases hC : (ω, Y ω) ∈ C
    · rcases hC with ⟨hωE, hf, hsine⟩
      have hdriver := normalizedRestartDriverPath_driver κ B hc τ a ω
      have hy' : IsCapacityTwoWitness
          (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
          (Φ (Y ω)) (Gc (Y ω)) (Fc (Y ω)) := hdriver ▸ hy
      have hf' : radiusLevelTime (Φ (Y ω)) (Gc (Y ω)) (w ω) 1 < ∞ := by
        rwa [canonicalRadiusLevel_eq κ (Y ω) hy 1 (by norm_num) (w ω)] at hf
      have hbase' : fullRadius (G ω) (τ ω)
          (F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ))) =
          (2 * (F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ))).im) *
            Real.exp (-u) := by simpa only [hpoint ω hωE] using hbase ω hωE
      have hang := (hw ω).normalized_restart_stopped_sine ((hc ω).const_mul _)
        (τ ω) (a ω) (ha ω) hy' (w ω) u 1 hbase' hf'
      rw [hpoint ω hωE] at hang
      have hphysical : ω ∈ S := by
        refine ⟨hωE, ?_, ?_⟩
        · rw [canonicalRadiusLevel_eq κ (bp ω) (hw ω) (u + 1) (by linarith) z]
          exact hang.1
        · rw [canonicalStoppedSine_eq κ (bp ω) (hw ω) (u + 1) (by linarith) z hang.1]
          change s ≤ Real.sin (Complex.arg (G ω (radiusLevelTime (γ ω) (G ω) z
            (u + 1)).toNNReal z - (Real.sqrt κ * B (radiusLevelTime (γ ω) (G ω) z
              (u + 1)).toNNReal ω : ℝ)))
          rw [hang.2]
          rw [canonicalStoppedSine_eq κ (Y ω) hy 1 (by norm_num) (w ω) hf'] at hsine
          rw [← hdriver]
          exact hsine
      rw [indicator_of_mem (show (ω, Y ω) ∈ C from ⟨hωE, hf, hsine⟩),
        indicator_of_mem hphysical]
      change M ω * canonicalFiniteDensity κ (1, w ω, Y ω) ≤ Z ω
      rw [hMω hωE, canonicalFiniteDensity_eq κ (Y ω) hy 1 (by norm_num) (w ω), hdriver,
        ← ENNReal.ofReal_mul
          (div_nonneg (greenDensity_nonneg (hw ω) κ (τ ω) z) (initialGreen_pos κ z hz).le)]
      apply ENNReal.ofReal_le_ofReal
      have hbound := (hw ω).normalized_restart_stopped_green_lower ((hc ω).const_mul _)
        (τ ω) (a ω) (ha ω) hy' κ (w ω) (hgeometry ω hωE).2.1 u 1 hbase'
      rw [hpoint ω hωE] at hbound
      calc
        _ = (greenDensity κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (τ ω) z *
          (stoppedGreen κ (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω)
            (τ ω) (a ω)) (Φ (Y ω)) (Gc (Y ω)) (w ω) 1 / initialGreen κ (w ω))) /
            initialGreen κ z := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hbound (initialGreen_pos κ z hz).le
    · rw [indicator_of_notMem hC]
      exact bot_le
  have h := restart_weighted_event_lower_bound P ν hτ.measurableSpace hτ.measurableSpace_le
    Y hYm hYlaw K hKm C hCm (E.indicator M) Z (ENNReal.ofReal (1 / 2 : ℝ))
    ENNReal.ofReal_ne_top S hSm hsec hactual A hA
  rw [setLIntegral_indicator (hτ.measurableSpace_le E hE), inter_comm E A, hMpast A hA] at h
  simpa only [Z, S, bp, finiteCenteredLaw, ← inter_assoc] using h

end SLEExactGauge

end

end OAI
