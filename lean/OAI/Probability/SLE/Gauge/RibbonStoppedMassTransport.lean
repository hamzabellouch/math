import OAI.Probability.SLE.Gauge.RibbonPrefixTransport
import OAI.Probability.SLE.Gauge.RibbonStepSuccess

namespace OAI

/-! Exact spatial and capacity transport of a completed ribbon's stopped
mass. The completion is the actual first front of the transported trace. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage FrontClockChange ScaleTraceLaw
open FrontSuccessMeasurability RibbonPassageScaling

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma firstFrontTime_scalePath_of_finite
    (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0, ℂ)) (g g' : C(ℂ, ℝ))
    (hgg' : ∀ z : ℂ, g' ((c : ℂ) * z) = g z) (k : ℝ) (T : ℝ≥0)
    (hT : firstFrontTime (fun t => g (p t)) k = (T : WithTop ℝ≥0)) :
    firstFrontTime (fun t => g' (scalePath c p t)) k = ((c ^ 2 * T : ℝ≥0) : WithTop ℝ≥0) := by
  let e := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
  have heval (t : ℝ≥0) : scalePath c p (e t) = (c : ℂ) * p t :=
    scalePath_at_scaled_time c hc p t
  have hclock : (fun t => g' (scalePath c p (e t))) = (fun t => g (p t)) := by
    funext t
    rw [heval, hgg']
  have hhit := firstFrontTime_attained _ (g.continuous.comp p.continuous) k T hT
  exact firstFrontTime_of_clock_hit e (fun t => g' (scalePath c p t)) k T
    (by rw [hclock]; exact hT) (by rw [heval, hgg']; exact hhit)

lemma segmentSausageCharge_scalePath
    (κ : ℝ) (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0, ℂ)) (T : ℝ≥0)
    {v : ℝ} (hv : 0 < v) (D : Set ℂ) :
    segmentSausageCharge κ (scalePath c p) 0 (c ^ 2 * T) ((c : ℝ) * v) (affine 0 c '' D) =
      ENNReal.ofReal ((c : ℝ) ^ dimension κ) * segmentSausageCharge κ p 0 T v D := by
  let e := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
  have he0 : e 0 = 0 := by change c ^ 2 * 0 = 0; exact mul_zero _
  have hpath : (fun t => scalePath c p (e t)) = (fun t => affine 0 c (p t)) := by
    funext t
    change scalePath c p (c ^ 2 * t) = affine 0 c (p t)
    simpa only [affine, zero_add] using scalePath_at_scaled_time c hc p t
  calc
    _ = segmentSausageCharge κ (fun t => scalePath c p (e t)) 0 T ((c : ℝ) * v)
        (affine 0 c '' D) := by rw [segmentSausageCharge_clock, he0]; rfl
    _ = segmentSausageCharge κ (fun t => affine 0 c (p t)) 0 T ((c : ℝ) * v)
        (affine 0 c '' D) := by rw [hpath]
    _ = _ := segmentSausageCharge_affine κ 0 (show 0 < (c : ℝ) from hc) p 0 T hv D

def ribbonStoppedMassEvent (P : ℂ → ℂ) (g : C(ℂ, ℝ)) (k ε κ v : ℝ)
    (D : Set ℂ) (b : ℝ≥0∞) : Set C(ℝ≥0, ℂ) :=
  {p | p ∈ GoodRibbonPrefix (fun p : C(ℝ≥0, ℂ) => (p : ℝ≥0 → ℂ))
      (ribbonFrontStop g (fun p : C(ℝ≥0, ℂ) => (p : ℝ≥0 → ℂ)) k) P ε ∧
    b ≤ segmentSausageCharge κ p 0 ((firstFrontTime (fun t => g (p t)) k).untopD 0) v D}

lemma measurableSet_ribbonStoppedMassEvent
    (P : ℂ → ℂ) (he : Topology.IsClosedEmbedding (fun z : closedRibbon => P z))
    (g : C(ℂ, ℝ)) (k ε κ v : ℝ) (D : Set ℂ) (b : ℝ≥0∞) :
    MeasurableSet (ribbonStoppedMassEvent P g k ε κ v D b) := by
  let ℱ : Filtration ℝ≥0 (borel C(ℝ≥0, ℂ)) :=
    Filtration.const ℝ≥0 (borel C(ℝ≥0, ℂ)) le_rfl
  let γ := fun p : C(ℝ≥0, ℂ) => (p : ℝ≥0 → ℂ)
  have ha : Adapted ℱ (fun t p => γ p t) := by
    intro t
    change @Measurable C(ℝ≥0, ℂ) ℂ (borel C(ℝ≥0, ℂ)) _ (fun p => p t)
    exact (continuous_eval_const t).measurable
  have hτ := ribbonFrontStop_stopping ℱ g γ ha (fun p => p.continuous) k
  have hg : MeasurableSet (GoodRibbonPrefix γ (ribbonFrontStop g γ k) P ε) :=
    hτ.measurableSpace_le _ (goodRibbonPrefix_measurable ℱ γ ha (fun p => p.continuous) _ hτ P he ε)
  exact hg.inter (measurableSet_le measurable_const
    (segmentSausageCharge_measurable id measurable_id (fun _ => 0)
      (fun p => (firstFrontTime (fun t => g (p t)) k).untopD 0)
      measurable_const (hτ.measurable'.untopD 0) κ v D))

/-- Transport uses the same actual completed prefix and a deterministically
scaled mesh, region and mass threshold. -/
theorem mem_ribbonStoppedMassEvent_scalePath
    (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0, ℂ)) (P : ℂ → ℂ)
    (g g' : C(ℂ, ℝ)) (hgg' : ∀ z : ℂ, g' ((c : ℂ) * z) = g z)
    (k ε κ : ℝ) {v : ℝ} (hv : 0 < v) (D : Set ℂ) (b : ℝ≥0∞)
    (hp : p ∈ ribbonStoppedMassEvent P g k ε κ v D b) :
    scalePath c p ∈ ribbonStoppedMassEvent (fun z => (c : ℂ) * P z) g' k ε κ
      ((c : ℝ) * v) (affine 0 c '' D) (ENNReal.ofReal ((c : ℝ) ^ dimension κ) * b) := by
  have hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => (p : ℝ≥0 → ℂ))
      (fun _ => firstFrontTime (fun t => g (p t)) k) P ε := hp.1
  have hnew := goodRibbonPrefix_scalePath c hc p P g g' hgg' k ε hpref
  refine ⟨hnew, ?_⟩
  cases hT : firstFrontTime (fun t => g (p t)) k with
  | top => exact False.elim (hpref.1 hT)
  | coe T =>
    have ht := firstFrontTime_scalePath_of_finite c hc p g g' hgg' k T hT
    change _ ≤ segmentSausageCharge κ (scalePath c p) 0
      ((firstFrontTime (fun t => g' (scalePath c p t)) k).untopD 0) _ _
    rw [ht, WithTop.untopD_coe, segmentSausageCharge_scalePath κ c hc p T hv]
    apply mul_le_mul' le_rfl
    simpa only [hT, WithTop.untopD_coe] using hp.2

end SLEExactGauge

end

end OAI
