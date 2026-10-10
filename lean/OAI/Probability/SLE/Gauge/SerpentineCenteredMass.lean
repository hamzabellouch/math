import OAI.Probability.SLE.Gauge.SerpentineActualRadius
import OAI.Probability.SLE.Gauge.SerpentineActualAngleReflection
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! The stopped physical experiment under the actual finite centered law.
Both its mass and its successful completion are observable at the front. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates Target FirstFrontPassage

lemma experimentSteps_add_one {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) : experimentSteps s w m + 1 = fitCompletion s w m := by
  have hbound := (fitCompletion_bounds hs w hw hm).1
  have hEntry : 0 ≤ fitEntry s w m :=
    (by unfold fitHeight; positivity : (0 : ℝ) ≤ fitHeight m).trans (fit_entry_lower hs w hw hm)
  have hcol : 0 ≤ columnEntry 0 m (2 * m) := columnEntry_nonneg le_rfl _ _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : (0 : ℝ) < fitCompletion s w m := by linarith
  have hkN : 0 < fitCompletion s w m := by exact_mod_cast hk
  change fitCompletion s w m - 1 + 1 = fitCompletion s w m
  omega

lemma experiment_front_eq {Ω : Type*} {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) (g : C(ℂ, ℝ)) (γ : Ω → ℝ≥0 → ℂ) :
    ribbonIntegerFront g γ (experimentSteps s w m) =
      ribbonFrontStop g γ (fitCompletion s w m) := by
  have hh : (experimentSteps s w m : ℝ) + 1 = fitCompletion s w m := by
    exact_mod_cast experimentSteps_add_one hs w hw hm
  simp only [ribbonIntegerFront, hh]

lemma exponential_prefactor_quadratic_cost {p C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 0 < m →
      Real.exp (-D * (m : ℝ) ^ 2) ≤ p * Real.exp (-C * (m : ℝ) ^ 2) := by
  refine ⟨C + |Real.log p| + 1, by positivity, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : -|Real.log p| ≤ Real.log p := neg_abs_le _
  have hmul := mul_nonneg (abs_nonneg (Real.log p))
    (show 0 ≤ (m : ℝ) ^ 2 - 1 by nlinarith)
  calc
    _ ≤ Real.exp (Real.log p + -C * (m : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg (Real.log p)]
    _ = _ := by rw [Real.exp_add, Real.exp_log hp]

theorem uniform_serpentine_centered_stopped_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) :
    ∃ c v₀ : ℝ, 0 < c ∧ 0 < v₀ ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → s ≤ w.im → ∀ m : ℕ, 0 < m →
      ∀ v : ℝ, 0 < v → v < ribbonWidth (halfHeight s) m * v₀ → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (physicalExperimentChart s w m z) = z.re) →
      ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤
        finiteCenteredLaw μ κ B γ G w (experimentRadiusLevel s)
          (RibbonStepSuccess γ (fun _ => 0) (ribbonFrontStop g γ (fitCompletion s w m))
            (physicalExperimentChart s w m) ε κ v
            (c * (s / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ)
            (closedBall (center s w) (s / 20))) := by
  have hm (t : ℝ≥0) : Measurable (B t) :=
    hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨c, v₀, hcm, hv₀, hprob⟩ := uniform_serpentine_physical_stopped_mass μ κ hκ hκ8
    B hB hm hc γ G F hw hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW ε hε hεsmall
  refine ⟨c, v₀, hcm, hv₀, fun s hs hs1 => ?_⟩
  obtain ⟨C, hC, hprob⟩ := hprob s hs
  obtain ⟨s₀, hs₀, hangle⟩ := uniform_serpentine_actual_angle hplanar hstraight hexit hwiener W hW hs hs1
  obtain ⟨D, hD, hcost⟩ := exponential_prefactor_quadratic_cost
    (Real.rpow_pos_of_pos hs₀ (greenExponent κ)) hC
  refine ⟨D, hD, fun w hwn hwy m hmp v hv hvcut g hg => ?_⟩
  let τ := ribbonFrontStop g γ (fitCompletion s w m)
  let E := RibbonStepSuccess γ (fun _ => 0) τ (physicalExperimentChart s w m) ε κ v
    (c * (s / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ)
    (closedBall (center s w) (s / 20))
  let ℱ := Filtration.natural B
    (fun _t => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)
  have ha : Adapted ℱ (fun t ω => γ ω t) :=
    brownian_capacity_trace_adapted B hm hc κ γ G F hw
  have hγc : ∀ ω, Continuous (γ ω) := fun ω => (hw ω).1
  have hτ : IsStoppingTime ℱ τ := ribbonFrontStop_stopping ℱ g γ ha hγc _
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    ribbonStepSuccess_measurable ℱ γ ha hγc (fun _ => 0) τ
      (isStoppingTime_const ℱ 0) hτ (fun _ => bot_le) _
      (physicalExperimentChart_closedEmbedding hs w hwy hmp) ε κ v _ _
  have hordinary : ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤ μ E := by
    have hh := hprob w hwn hwy m hmp v hv hvcut g hg
    rw [experiment_front_eq hs w hwy hmp g γ] at hh
    simpa only [E, τ, RibbonStepSuccess, Set.ofPred_and, Set.ofPred_mem_eq,
      WithTop.untopD_zero] using hh
  have hcentered := finiteCenteredLaw_completed_experiment_lower_bound hB hBm hc hB0 κ hκ hκ8
    γ G F (Eventually.of_forall hw) w (show w ∈ upperHalfPlane from lt_of_lt_of_le hs hwy)
    (experimentRadiusLevel s) (experimentRadiusLevel_nonneg hs hs1) τ hτ E hE s₀ hs₀.le (by
      apply Eventually.of_forall
      intro ω hω
      have hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ ω) (fun _ => τ ω)
          (physicalExperimentChart s w m) ε := hω.1
      have hbefore := good_physicalExperiment_before_radius ((hc ω).const_mul _) (hw ω)
        hs w hwn hwy hmp (τ ω) ε hpref
      refine ⟨hpref.1, hbefore.1, hbefore.2, ?_⟩
      rw [Complex.sin_arg]
      simpa only [τ, ribbonFrontStop, Complex.ofReal_mul] using
        hangle _ _ _ _ (hw ω) ((hc ω).const_mul _) w hwn hwy m hmp g hg ε hεsmall hpref)
  calc
    _ ≤ ENNReal.ofReal (s₀ ^ greenExponent κ) *
        ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs₀.le _)]
      exact ENNReal.ofReal_le_ofReal (hcost m hmp)
    _ ≤ ENNReal.ofReal (s₀ ^ greenExponent κ) * μ E := mul_le_mul' le_rfl hordinary
    _ ≤ _ := hcentered

end SLEExactGauge.Serpentine

end

end OAI
