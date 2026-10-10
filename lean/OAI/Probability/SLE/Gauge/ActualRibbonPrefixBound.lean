import OAI.Probability.SLE.Gauge.ActualRibbonStep

namespace OAI

/-! Apply the proved actual conditional ribbon estimate on the measurable
physical prefix, then charge its mass to the two original global fronts. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage

local instance prefixBoundPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance prefixBoundPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem actual_ribbon_step_on_good_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (U : Ω → ℝ≥0 → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ ω, Continuous (U ω)) (hw : ∀ ω, IsCapacityTwoWitness (U ω) (γ ω) (G ω) (F ω))
    (C L : ℝ≥0) (hL : 0 < L) (ε κ v c : ℝ) (hε : ε ≤ 1 / 8) (q : ℝ≥0∞)
    (P : ℂ → ℂ) (hemb : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun t : ℝ => ‖P (t : ℂ)‖) atTop atTop)
    (g : C(ℂ, ℝ)) (hg : ∀ z ∈ closedRibbon, g (P z) = z.re)
    (hg0 : ∀ ω, g (γ ω 0) = 0) (k : ℝ) (hk : 1 ≤ k)
    (hu : ∀ j ∈ ({k, k + 1} : Set ℝ), LipschitzOnWith C P (ribbonStepPatch j))
    (hl : ∀ j ∈ ({k, k + 1} : Set ℝ), ∀ z ∈ ribbonStepPatch j,
      ∀ w ∈ ribbonStepPatch j, dist z w ≤ L * dist (P z) (P w))
    (hτ : IsStoppingTime ℱ (ribbonFrontStop g γ k))
    (hbound : ∀ E : Set Ω,
      (∀ᵐ ω ∂μ, ω ∈ E → ribbonFrontStop g γ k ω ≠ ⊤) →
      (∀ᵐ ω ∂μ, ω ∈ E → ActualRibbonAdmissible U γ G F C L ε κ v c
        (ribbonPathStep P C L ε k κ v c) ω ((ribbonFrontStop g γ k ω).untopD 0)) →
      ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A → A ⊆ E →
        q * μ A ≤ μ (A ∩ {ω | shiftedActualTrace γ (fun ω => (hw ω).1) ω
          ((ribbonFrontStop g γ k ω).untopD 0) ∈ ribbonPathStep P C L ε k κ v c}))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ GoodRibbonPrefix γ (ribbonFrontStop g γ k) P ε) :
    q * μ A ≤ μ (A ∩ RibbonStepSuccess γ (ribbonFrontStop g γ k)
      (ribbonFrontStop g γ (k + 1)) P ε κ v c (physicalMiddleRegion P closedRibbon k ε)) := by
  have hcert (ω : Ω) (hω : ω ∈ GoodRibbonPrefix γ (ribbonFrontStop g γ k) P ε) :
      ∃ d : RibbonHistory C L ε, d.U = U ω ∧ d.trace = γ ω ∧ d.forward = G ω ∧
        d.inverse = F ω ∧ d.chart = P ∧ d.front = k ∧
        d.time = (ribbonFrontStop g γ k ω).untopD 0 := by
    obtain ⟨d, hU', hγ', hG', hF', hP', hk', ht⟩ :=
      actual_history_of_goodRibbonPrefix (U ω) (γ ω) (G ω) (F ω) (hU ω) (hw ω)
        P hemb hP hi hH hescape g hg (hg0 ω) k hk hω (hu k (by simp)) (hl k (by simp))
    refine ⟨d, hU', hγ', hG', hF', hP', hk', ?_⟩
    have hh := congrArg (fun t : WithTop ℝ≥0 => t.untopD 0) ht
    simpa only [WithTop.untopD_coe, ribbonFrontStop] using hh
  have hstates : ∀ᵐ ω ∂μ, ω ∈ GoodRibbonPrefix γ (ribbonFrontStop g γ k) P ε →
      ActualRibbonAdmissible U γ G F C L ε κ v c (ribbonPathStep P C L ε k κ v c)
        ω ((ribbonFrontStop g γ k ω).untopD 0) := by
    apply Filter.Eventually.of_forall
    intro ω hω
    obtain ⟨d, hU', hγ', hG', hF', hP', hk', ht⟩ := hcert ω hω
    exact ⟨d, hU', hγ', hG', hF', ht, by rw [d.stepEvent_eq_ribbonPathStep, hP', hk']⟩
  have hb := hbound (GoodRibbonPrefix γ (ribbonFrontStop g γ k) P ε)
    (Filter.Eventually.of_forall (fun _ hω => hω.1)) hstates A hA hAE
  apply hb.trans (measure_mono ?_)
  intro ω hω
  refine ⟨hω.1, ?_⟩
  obtain ⟨d, hU', hγ', hG', hF', hP', hk', ht⟩ := hcert ω (hAE hω.1)
  have he : d.futureTrace = shiftedActualTrace γ (fun ω => (hw ω).1) ω
      ((ribbonFrontStop g γ k ω).untopD 0) := by
    ext t
    simp only [RibbonHistory.futureTrace, shiftedActualTrace, ContinuousMap.coe_mk, hγ', ht]
  have hstep : d.futureTrace ∈ d.stepEvent κ v c := by
    rw [he, d.stepEvent_eq_ribbonPathStep, hP', hk']
    exact hω.2
  have hh := d.actual_step_success hε hL κ v c g (by rw [hP']; exact hg) hstep
    (by rw [hP', hk']; exact hu _ (by simp)) (by rw [hP', hk']; exact hl _ (by simp))
  simpa only [RibbonStepSuccess, GoodRibbonPrefix, mem_inter_iff, mem_ofPred_eq,
    hγ', hP', hk', ribbonFrontStop] using hh

end SLEExactGauge

end

end OAI
