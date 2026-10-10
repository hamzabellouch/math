import OAI.Analysis.KadisonKastler.CoreTraceReciprocal

namespace OAI

/-! # Simple packets in the unit frequency window -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem unitWindow_indicator_scalar (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
      (indicatorConstLp 2 hs hfin (1 : ℂ)) =
      regularIndicatorProjection s hs unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc (indicatorConstLp 2 hs hfin (1 : ℂ)),
    regularIndicatorProjection_apply_ae s hs unitFrequencyScalar,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℂ)),
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))]
      with t hp hq hs' hw
  change unitFrequencyScalar t = _ at hw
  rw [hp, hq]
  by_cases hts : t ∈ s <;> by_cases htw : t ∈ Set.Ioc (0 : ℝ) 1 <;>
    simp [hts, htw, hs', hw]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTensorVector_indicator (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) (x : H) :
    regularTensorVector (indicatorConstLp 2 hs hfin (1 : ℂ)) x =
      indicatorConstLp 2 hs hfin x := by
  apply Lp.ext
  filter_upwards [regularTensorVector_apply_ae (indicatorConstLp 2 hs hfin (1 : ℂ)) x,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := x)]
      with t ht h1 hx
  rw [ht, h1, hx]
  by_cases hts : t ∈ s <;> simp [hts]

theorem unitWindow_indicator_packet (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) (x : H) :
    regularFrequencyWindow 0 1
      ((Lp.fourierTransformₗᵢ ℝ H).symm (indicatorConstLp 2 hs hfin x)) =
      regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) x := by
  rw [← regularTensorVector_indicator s hs hfin x]
  change regularFrequencyWindow 0 1
    (regularFrequencyPacket (indicatorConstLp 2 hs hfin (1 : ℂ)) x) = _
  rw [regularFrequencyWindow_packet, unitWindow_indicator_scalar]

end

end KadisonKastler

end OAI
