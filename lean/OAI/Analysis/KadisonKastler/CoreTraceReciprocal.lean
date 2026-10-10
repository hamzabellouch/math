import OAI.Analysis.KadisonKastler.CoreTraceFrequencyVector
import OAI.Analysis.KadisonKastler.RegularActionPackets

namespace OAI

/-! # A bounded reciprocal for the core trace packet

The reciprocal is cut off outside the unit frequency window. Its
spectral multiplier recovers the unweighted unit packet exactly.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def coreTraceReciprocal (t : ℝ) : ℂ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun s => (Real.exp (Real.pi * (1 - s)) : ℂ)) t

theorem coreTraceReciprocal_measurable : Measurable coreTraceReciprocal :=
  (show Continuous (fun s : ℝ => (Real.exp (Real.pi * (1 - s)) : ℂ)) by
    fun_prop).measurable.indicator measurableSet_Ioc

theorem coreTraceReciprocal_bound (t : ℝ) :
    ‖coreTraceReciprocal t‖ ≤ Real.exp Real.pi := by
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [coreTraceReciprocal, Set.indicator_of_mem ht,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, ht.1]
  · simp only [coreTraceReciprocal, Set.indicator_of_notMem ht, norm_zero]
    exact (Real.exp_pos _).le

theorem coreTraceReciprocal_scalar :
    regularScalarMultiplier coreTraceReciprocal coreTraceReciprocal_measurable
      (Real.exp Real.pi) coreTraceReciprocal_bound coreTraceFrequencyScalar =
      unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularScalarMultiplier_apply_ae coreTraceReciprocal
      coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound
      coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hm hw hu
  change unitFrequencyScalar t = _ at hu
  rw [hm, hw, hu]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [coreTraceReciprocal, coreTraceFrequencyFunction,
      Set.indicator_of_mem ht, smul_eq_mul, ← Complex.ofReal_mul, ← Real.exp_add]
    norm_num [show Real.pi * (1 - t) + Real.pi * (t - 1) = 0 by ring]
  · simp [coreTraceReciprocal, coreTraceFrequencyFunction, ht]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceReciprocal_packet
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω) :
    regularActionMultiplier U hU coreTraceReciprocal coreTraceReciprocal_measurable
      (Real.exp Real.pi) coreTraceReciprocal_bound (coreTraceFrequencyVector Ω) =
      unitFrequencyVector Ω := by
  rw [coreTraceFrequencyVector, regularActionMultiplier_packet U hU Ω hΩ,
    coreTraceReciprocal_scalar]
  rfl

end

end KadisonKastler

end OAI
