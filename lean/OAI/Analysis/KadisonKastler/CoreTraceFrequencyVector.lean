import OAI.Analysis.KadisonKastler.CoreFrequencyUnitWindow

namespace OAI

/-! # The bounded-frequency vector for the core trace

The scalar weight is exp(pi (s-1)) on (0,1], in the Fourier convention
exp(-2 pi i t s). The corresponding vector has explicit L2 bounds and frequency support.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def coreTraceFrequencyFunction (t : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun s => (Real.exp (Real.pi * (s - 1)) : ℂ)) t

theorem coreTraceFrequencyFunction_memLp :
    MemLp coreTraceFrequencyFunction 2 (volume : Measure ℝ) := by
  have hbase : MemLp ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 2
      (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr (by simp [Real.volume_Ioc]))
  apply hbase.mono
  · exact (show Continuous (fun s : ℝ => (Real.exp (Real.pi * (s - 1)) : ℂ)) by
      fun_prop).aestronglyMeasurable.indicator measurableSet_Ioc
  · apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · simp only [coreTraceFrequencyFunction, Set.indicator_of_mem ht, norm_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ht.2])
    · simp [coreTraceFrequencyFunction, ht]

def coreTraceFrequencyScalar : Lp ℂ 2 (volume : Measure ℝ) :=
  coreTraceFrequencyFunction_memLp.toLp coreTraceFrequencyFunction

theorem coreTraceFrequencyScalar_apply_ae :
    coreTraceFrequencyScalar =ᵐ[volume] coreTraceFrequencyFunction :=
  coreTraceFrequencyFunction_memLp.coeFn_toLp

theorem coreTraceFrequencyScalar_norm_le_one : ‖coreTraceFrequencyScalar‖ ≤ 1 := by
  rw [← norm_unitFrequencyScalar]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coreTraceFrequencyScalar_apply_ae,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hw hu
  change ‖coreTraceFrequencyScalar t‖ ≤ ‖unitFrequencyScalar t‖
  change unitFrequencyScalar t = _ at hu
  rw [hw, hu]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [coreTraceFrequencyFunction, Set.indicator_of_mem ht, norm_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ht.2])
  · simp [coreTraceFrequencyFunction, ht]

theorem coreTraceFrequencyScalar_norm_lower :
    Real.exp (-Real.pi) ≤ ‖coreTraceFrequencyScalar‖ := by
  have h := Lp.norm_le_norm_of_ae_le (f := (Real.exp (-Real.pi) : ℂ) • unitFrequencyScalar)
    (g := coreTraceFrequencyScalar) (by
      filter_upwards [Lp.coeFn_smul (Real.exp (-Real.pi) : ℂ) unitFrequencyScalar,
        (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
          (μ := volume) (hs := measurableSet_Ioc)
          (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ))),
        coreTraceFrequencyScalar_apply_ae] with t hc hu hw
      change unitFrequencyScalar t = _ at hu
      rw [hc, Pi.smul_apply, hu, hw]
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · simp only [coreTraceFrequencyFunction, Set.indicator_of_mem ht, smul_eq_mul,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht.1])
      · simp [coreTraceFrequencyFunction, ht])
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_unitFrequencyScalar, mul_one] using h

theorem coreTraceFrequencyScalar_norm_pos : 0 < ‖coreTraceFrequencyScalar‖ :=
  (Real.exp_pos _).trans_le coreTraceFrequencyScalar_norm_lower

theorem coreTraceFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc coreTraceFrequencyScalar =
      coreTraceFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae] with t hp ht
  change regularIndicatorProjection _ _ coreTraceFrequencyScalar t = coreTraceFrequencyScalar t
  rw [hp]
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · exact Set.indicator_of_mem h _
  · rw [Set.indicator_of_notMem h, ht]
    simp [coreTraceFrequencyFunction, h]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coreTraceFrequencyVector (Ω : H) : RegularCoreHilbert H :=
  regularFrequencyPacket coreTraceFrequencyScalar Ω

theorem coreTraceFrequencyVector_fixed (Ω : H) :
    regularFrequencyWindow 0 1 (coreTraceFrequencyVector Ω) = coreTraceFrequencyVector Ω := by
  rw [coreTraceFrequencyVector, regularFrequencyWindow_packet, coreTraceFrequencyScalar_fixed]

theorem coreTraceFrequencyVector_norm_le (Ω : H) : ‖coreTraceFrequencyVector Ω‖ ≤ ‖Ω‖ := by
  rw [coreTraceFrequencyVector, norm_regularFrequencyPacket]
  exact (mul_le_mul_of_nonneg_right coreTraceFrequencyScalar_norm_le_one (norm_nonneg Ω)).trans_eq
    (one_mul _)

theorem coreTraceFrequencyVector_ne_zero {Ω : H} (hΩ : Ω ≠ 0) :
    coreTraceFrequencyVector Ω ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [coreTraceFrequencyVector, norm_regularFrequencyPacket]
  exact mul_ne_zero coreTraceFrequencyScalar_norm_pos.ne' (norm_ne_zero_iff.mpr hΩ)

end

end KadisonKastler

end OAI
