import OAI.Probability.SLE.Gauge.RibbonGoodPrefix

namespace OAI

/-! Actual passage-and-mass successes are measured in the next global
front past, with the earlier global front as the mass window's start. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage FrontSuccessMeasurability

local instance stepSuccessPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stepSuccessPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def RibbonStepSuccess {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (σ τ : Ω → WithTop ℝ≥0) (P : ℂ → ℂ) (ε κ v c : ℝ) (R : Set ℂ) : Set Ω :=
  GoodRibbonPrefix γ τ P ε ∩ {ω | ENNReal.ofReal c ≤
    segmentSausageCharge κ (γ ω) ((σ ω).untopD 0) ((τ ω).untopD 0) v R}

lemma stoppedAtPath_eq_on_prefix (f : C(ℝ≥0, ℂ)) (t : ℝ≥0) :
    EqOn (stoppedAtPath f (t : WithTop ℝ≥0)) f (Icc 0 t) := by
  intro u hu
  simp only [stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe,
    clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk, min_eq_left hu.2,
    max_eq_right hu.1]

lemma segmentSausageCharge_shift
    (κ : ℝ) (γ : ℝ≥0 → ℂ) (T S : ℝ≥0) (v : ℝ) (R : Set ℂ) :
    segmentSausageCharge κ (fun t => γ (T + t)) 0 S v R =
      segmentSausageCharge κ γ T (T + S) v R := by
  have hs : sourceSausageSet (fun t => γ (T + t)) 0 S v =
      sourceSausageSet γ T (T + S) v := by
    ext z
    constructor
    · rintro ⟨t, ht, hd⟩
      exact ⟨T + t, ⟨le_add_of_nonneg_right bot_le, add_le_add le_rfl ht.2⟩, hd⟩
    · rintro ⟨t, ht, hd⟩
      refine ⟨t - T, ⟨bot_le, ?_⟩, ?_⟩
      · exact (tsub_le_iff_right).mpr (by simpa only [add_comm] using ht.2)
      · simpa only [add_tsub_cancel_of_le ht.1] using hd
  simp only [segmentSausageCharge, hs]

/-- The whole actual step and its sausage lower bound are adapted to the
next front. Both global front times may be infinite off success. -/
theorem ribbonStepSuccess_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω))
    (σ τ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) (P : ℂ → ℂ)
    (he : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (ε κ v c : ℝ) (R : Set ℂ) :
    MeasurableSet[hτ.measurableSpace] (RibbonStepSuccess γ σ τ P ε κ v c R) := by
  let f := fun ω => stoppedAtPath (sourceTracePath γ hc ω) (τ ω)
  have hfm : Measurable[hτ.measurableSpace] f := stoppedAtPath_measurable ℱ γ ha hc τ hτ
  have htm : Measurable[hτ.measurableSpace] (fun ω => (τ ω).untopD 0) := hτ.measurable.untopD 0
  have hsm : Measurable[hτ.measurableSpace] (fun ω => (σ ω).untopD 0) :=
    (hσ.measurable.mono (IsStoppingTime.measurableSpace_mono hσ hτ hστ) le_rfl).untopD 0
  have hgood := goodRibbonPrefix_measurable ℱ γ ha hc τ hτ P he ε
  let : MeasurableSpace Ω := hτ.measurableSpace
  have hm := hgood.inter
    (measurableSet_le (measurable_const : Measurable (fun _ : Ω => ENNReal.ofReal c))
      (segmentSausageCharge_measurable f hfm _ _ hsm htm κ v R))
  convert hm using 1
  ext ω
  by_cases hω : ω ∈ GoodRibbonPrefix γ τ P ε
  · have ht := hω.1
    lift τ ω to ℝ≥0 using ht with t hτt
    have hs := sourceSausageSet_congr_interval
      (s := (σ ω).untopD 0) (t := t)
      (fun u hu => stoppedAtPath_eq_on_prefix (sourceTracePath γ hc ω) t
        ⟨bot_le, hu.2⟩) v
    simp only [RibbonStepSuccess, mem_inter_iff, mem_ofPred_eq, hω, true_and,
      f, ← hτt, WithTop.untopD_coe, segmentSausageCharge, hs]
    rfl
  · simp only [RibbonStepSuccess, mem_inter_iff, mem_ofPred_eq, hω, false_and]

end SLEExactGauge

end

end OAI
