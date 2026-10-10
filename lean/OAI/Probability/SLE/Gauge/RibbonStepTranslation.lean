import OAI.Probability.SLE.Gauge.UniformActualRibbonPassage
import OAI.Probability.SLE.Gauge.LocalAffinePassage
import OAI.Probability.SLE.Gauge.RibbonMiddleMass

namespace OAI

/-! The recentered passage uses precisely the original ribbon coordinate
and original middle strip after translating back by the actual tip. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates RibbonPassageScaling BoundaryScaleLaw

def RibbonHistory.stepChart {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (z : ℂ) : ℂ := d.chart ((d.front : ℂ) + z)

lemma RibbonHistory.stepCompact_maps {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) :
    MapsTo (fun z : ℂ => (d.front : ℂ) + z) ribbonStepCompact closedRibbon := by
  intro z hz
  change 0 ≤ d.front + z.re ∧ |0 + z.im| ≤ 1
  exact ⟨by linarith [d.front_ge_one, hz.1], by simpa using hz.2.2.trans (by norm_num)⟩

lemma RibbonHistory.recenteredChart_injOn {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) : InjOn d.recenteredChart ribbonStepCompact := by
  intro u hu v hv huv
  have he := d.chart_injective (d.stepCompact_maps hu) (d.stepCompact_maps hv)
    (sub_left_inj.mp huv)
  exact add_left_cancel he

lemma RibbonHistory.step_progress_agrees {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) :
    ∀ z ∈ d.recenteredChart '' ribbonStepCompact,
      longitudinalCoordinate d.chart closedRibbon d.front (affine (d.trace d.time) 1 z) =
        longitudinalCoordinate d.recenteredChart ribbonStepCompact 0 z := by
  rintro z ⟨w, hw, rfl⟩
  have he : affine (d.trace d.time) 1 (d.recenteredChart w) =
      d.chart ((d.front : ℂ) + w) := by
    simp only [affine, Complex.ofReal_one, one_mul, RibbonHistory.recenteredChart]
    abel
  rw [he]
  simp only [longitudinalCoordinate,
    coordinateInverse_left d.chart_injective (d.stepCompact_maps hw),
    coordinateInverse_left d.recenteredChart_injOn hw, Complex.add_re,
    Complex.ofReal_re, add_sub_cancel_left, sub_zero]

lemma RibbonHistory.affine_recentered {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) :
    (fun z => affine (d.trace d.time) 1 (d.recenteredChart z)) = d.stepChart := by
  funext z
  simp only [affine, Complex.ofReal_one, one_mul, RibbonHistory.recenteredChart,
    RibbonHistory.stepChart]
  abel

lemma RibbonHistory.passage_translate {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) :
    affine (d.trace d.time) 1 ''
        physicalPassageRegion d.recenteredChart ribbonStepCompact C ε (ε / L) =
      physicalPassageRegion d.stepChart ribbonStepCompact C ε (ε / L) := by
  unfold physicalPassageRegion
  rw [← image_comp]
  exact congrArg (fun f : ℂ → ℂ => f '' _) d.affine_recentered

lemma RibbonHistory.middle_translate {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (hε : ε ≤ 1 / 8) :
    affine (d.trace d.time) 1 ''
        physicalMiddleRegion d.recenteredChart ribbonStepCompact 0 ε =
      physicalMiddleRegion d.chart closedRibbon d.front ε := by
  unfold physicalMiddleRegion
  rw [← image_comp]
  rw [show affine (d.trace d.time) 1 ∘ d.recenteredChart = d.stepChart from
    d.affine_recentered]
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hwl, hwu, hwi⟩, rfl⟩
    refine ⟨(d.front : ℂ) + w, ⟨d.stepCompact_maps hw, ?_, ?_, ?_⟩, rfl⟩
    · simpa only [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, sub_zero] using hwl
    · simpa only [Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, sub_zero] using hwu
    · simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hwi
  · rintro ⟨w, ⟨_, hwl, hwu, hwi⟩, rfl⟩
    refine ⟨w - (d.front : ℂ), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · change -(1 / 2 : ℝ) ≤ w.re - d.front ∧ w.re - d.front ≤ 5 / 2 ∧
        |w.im - 0| ≤ 1 / 2
      exact ⟨by linarith, by linarith, by simpa using hwi.le.trans (by linarith)⟩
    · simpa only [Complex.sub_re, Complex.ofReal_re, sub_zero] using hwl
    · simpa only [Complex.sub_re, Complex.ofReal_re, sub_zero] using hwu
    · simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hwi
    · simp only [RibbonHistory.stepChart, add_sub_cancel]

/-- Translating the actual finite boundary image back to its original tip
preserves the full probability, including the original middle-strip mass. -/
theorem RibbonHistory.frontMass_probability_translate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) (hε : ε ≤ 1 / 8)
    (η : Ω → ℝ≥0 → ℂ) (κ v c : ℝ) (hv : 0 < v) :
    P {ω | (fun t => affine (d.trace d.time) 1 (η ω t)) ∈
        {f : ℝ≥0 → ℂ | f ∈ PassageSuccess.FrontSuccess
          (fun _ (f : ℝ≥0 → ℂ) => f)
          (fun _ => longitudinalCoordinate d.chart closedRibbon d.front) (fun _ => 0)
          (fun _ => physicalPassageRegion d.stepChart ribbonStepCompact C ε (ε / L))
          (fun _ => d.chart ((d.front : ℂ) + 1)) (ε / L) 0 ∧
          ENNReal.ofReal c ≤ segmentSausageCharge κ f 0
            (FirstFrontPassage.frontTime
              (fun t => longitudinalCoordinate d.chart closedRibbon d.front (f t)) 1)
            v (physicalMiddleRegion d.chart closedRibbon d.front ε)}} =
      P {ω | η ω ∈ PassageSuccess.FrontSuccess
          (fun _ (f : ℝ≥0 → ℂ) => f)
          (fun _ => longitudinalCoordinate d.recenteredChart ribbonStepCompact 0) (fun _ => 0)
          (fun _ => physicalPassageRegion d.recenteredChart ribbonStepCompact C ε (ε / L))
          (fun _ => d.recenteredChart 1) (ε / L) 0 ∧
        ENNReal.ofReal c ≤ segmentSausageCharge κ (η ω) 0
          (FirstFrontPassage.frontTime
            (fun t => longitudinalCoordinate d.recenteredChart ribbonStepCompact 0 (η ω t)) 1)
          v (physicalMiddleRegion d.recenteredChart ribbonStepCompact 0 ε)} := by
  have hh := frontSuccess_mass_probability_affine_local P
    (fun _ => η) (fun _ => longitudinalCoordinate d.recenteredChart ribbonStepCompact 0)
    (fun _ => longitudinalCoordinate d.chart closedRibbon d.front) (fun _ => 0)
    (fun _ => physicalPassageRegion d.recenteredChart ribbonStepCompact C ε (ε / L))
    (fun _ => d.recenteredChart 1) (ε / L) (d.trace d.time) (by norm_num : (0 : ℝ) < 1) 0
    (fun z hz => d.step_progress_agrees z (image_mono inter_subset_left hz))
    κ (physicalMiddleRegion d.recenteredChart ribbonStepCompact 0 ε) hv c
  have htarget : affine (d.trace d.time) 1 (d.recenteredChart 1) =
      d.chart ((d.front : ℂ) + 1) := congrFun d.affine_recentered 1
  simpa only [d.passage_translate, d.middle_translate hε, htarget, one_mul,
    Real.one_rpow, mul_one, mem_ofPred_eq, PassageSuccess.FrontSuccess] using hh

end SLEExactGauge

end

end OAI
