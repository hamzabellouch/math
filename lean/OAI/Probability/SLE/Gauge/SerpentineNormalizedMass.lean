import OAI.Probability.SLE.Gauge.ActualRibbonStoppedMass
import OAI.Probability.SLE.Gauge.SerpentineInitialPrefix
import OAI.Probability.SLE.Gauge.SerpentineRetentionCount

namespace OAI

/-! The concrete connector and serpentine instantiate the actual stopped
iteration. All m² selected strip masses are present by completion, with
one positive initial probability and universal one-step constants. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates Target

def experimentEntry (s : ℝ) (w : ℂ) (m : ℕ) : ℝ :=
  connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)

def experimentSteps (s : ℝ) (w : ℂ) (m : ℕ) : ℕ := completionStep (experimentEntry s w m) m - 1

def normalizedExperimentDisk (s : ℝ) (w : ℂ) (m : ℕ) : Set ℂ :=
  (fun z : ℂ => (ribbonWidth (halfHeight s) m : ℂ) * z) ⁻¹' closedBall (center s w) (s / 20)

lemma retained_middle_in_normalized_disk {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : ε ≤ 1) :
    ∀ k ∈ retainedSteps (experimentEntry s w m) m,
      physicalMiddleRegion (experimentChart s w m) closedRibbon k ε ⊆ normalizedExperimentDisk s w m := by
  intro k hk z hz
  obtain ⟨⟨j, i⟩, _, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨a, ⟨ha, hl, hu, hi⟩, rfl⟩ := hz
  change (ribbonWidth (halfHeight s) m : ℂ) * experimentChart s w m a ∈ closedBall (center s w) (s / 20)
  rw [← physicalExperimentChart_eq]
  dsimp only [experimentEntry] at hl hu
  exact physicalExperimentChart_retained_disk hs w hw hm j.isLt i.isLt
    ⟨by linarith, by linarith⟩ (hi.le.trans hε)

/-- The actual normalized dense experiment, conditional only on the
recorded published inputs. Completion is finite on success and all mass
belongs to the stopped prefix at the prescribed common mesh. -/
theorem uniform_serpentine_normalized_stopped_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
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
    ∃ q₀ : ℝ≥0∞, ∃ q c v₀ : ℝ, 0 < q₀ ∧ q₀ ≤ 1 ∧ 0 < q ∧ q ≤ 1 ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ v : ℝ, 0 < v → v < v₀ → ∀ s : ℝ, 0 < s → ∀ w : ℂ, s ≤ w.im →
      ∀ m : ℕ, 0 < m → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (experimentChart s w m z) = z.re) →
      ENNReal.ofReal q ^ experimentSteps s w m * q₀ ≤ μ {ω |
        ω ∈ GoodRibbonPrefix γ (ribbonIntegerFront g γ (experimentSteps s w m)) (experimentChart s w m) ε ∧
        ((m ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal c ≤ segmentSausageCharge κ (γ ω) 0
          ((ribbonIntegerFront g γ (experimentSteps s w m) ω).untopD 0) v (normalizedExperimentDisk s w m)} := by
  obtain ⟨q, c, v₀, hq, hq1, hcm, hv₀, hiter⟩ := uniform_actual_ribbon_iteration μ κ hκ hκ8
    B hB hm hc γ G F hw hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW
    2 2 (by norm_num) (by norm_num) ε hε hεsmall
  have ha := brownian_capacity_trace_adapted B hm hc κ γ G F hw
  have hγc : ∀ ω, Continuous (γ ω) := fun ω => (hw ω).1
  have hSLE : IsOrdinaryChordalSLE κ γ μ :=
    ⟨fun t => (ha t).mono (Filtration.le _ t) le_rfl, B, hB,
      Filter.Eventually.of_forall (fun ω => ⟨G ω, F ω, hw ω⟩)⟩
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨q₀, hq₀, hinit⟩ := uniform_experiment_initial_goodPrefix_probability μ κ γ hSLE hsupport hε hε1
  refine ⟨min q₀ 1, q, c, v₀, lt_min hq₀ (by norm_num), min_le_right _ _, hq, hq1, hcm, hv₀, ?_⟩
  intro v hv hvcut s hs w hwy m hmp g hg
  obtain ⟨hP, hi, hpatch, hH, hinitial⟩ := experimentChart_geometry hs w hwy hmp
  have hemb := experimentChart_closedEmbedding hs w hwy hmp
  have hP0 : experimentChart s w m 0 = 0 := by
    simpa only [mul_zero] using hinitial 0 (by constructor <;> norm_num) (by norm_num)
  have hg0 (ω : Ω) : g (γ ω 0) = 0 := by
    rw [(hw ω).2.1, ← hP0]
    exact hg 0 (by constructor <;> norm_num)
  have hA : 0 ≤ experimentEntry s w m :=
    (by unfold fitHeight; positivity : (0 : ℝ) ≤ fitHeight m).trans (fit_entry_lower hs w hwy hmp)
  have hb := hiter v hv hvcut _ hemb hP.continuousOn hi hP0 hH
    (experimentChart_escape s w m) (fun k => (hpatch k).1) (fun k => (hpatch k).2)
    g hg (experimentSteps s w m)
  calc
    _ ≤ ENNReal.ofReal q ^ experimentSteps s w m *
        μ (GoodRibbonPrefix γ (ribbonIntegerFront g γ 0) (experimentChart s w m) ε) := by
      apply mul_le_mul' le_rfl
      apply (min_le_left q₀ 1).trans
      simpa only [ribbonIntegerFront, Nat.cast_zero, zero_add] using hinit s hs w hwy m hmp g hg
    _ ≤ _ := hb.trans (measure_mono (by
      intro ω hω
      have hI : ∀ i ∈ retainedSteps (experimentEntry s w m) m, 0 < i ∧ i ≤ experimentSteps s w m := by
        intro i hiI
        obtain ⟨hi0, hic⟩ := retainedSteps_bounds hA hmp i hiI
        exact ⟨hi0, by dsimp only [experimentSteps]; omega⟩
      have hh := actual_successes_force_stopped_mass γ hγc g hg0 _ hplanar hP.continuousOn hi
        ε κ v c hε1 (experimentSteps s w m) (retainedSteps (experimentEntry s w m) m) hI _
        (retained_middle_in_normalized_disk hs w hwy hmp hε1) ω hω
      simpa only [mem_ofPred_eq, retainedSteps_card hA hmp] using hh))

end SLEExactGauge.Serpentine

end

end OAI
