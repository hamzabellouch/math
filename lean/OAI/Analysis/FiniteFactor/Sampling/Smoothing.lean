import OAI.Analysis.FiniteFactor.Sampling.KernelTail

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate ENNReal
noncomputable section

theorem samplingCharacter_sub_argument (v : ℤ) (t u : ℝ) :
    samplingCharacter v (t-u) = samplingCharacter v t * samplingCharacter (-v) u := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem samplingCharacter_fract (v : ℤ) (t : ℝ) :
    samplingCharacter v (Int.fract t) = samplingCharacter v t := by
  simpa only [samplingCharacter, mul_assoc] using fourier_fract v t

theorem samplingKernel_fract (H : ℕ) (t : ℝ) :
    samplingKernel H (Int.fract t) = samplingKernel H t := by
  simp only [samplingKernel, samplingCharacter_fract]

theorem samplingKernel_shift_integral (H : ℕ) (hH : 0 < H) (t : ℝ) :
    (∫ u, samplingKernel H (t-u) ∂unitIntervalMeasure) = 1 := by
  have hc : (∫ u, (samplingKernel H (t-u) : ℂ) ∂unitIntervalMeasure) = 1 := by
    simp_rw [samplingKernel_expansion, samplingCharacter_sub_argument]
    rw [integral_const_mul, integral_finsetSum _ (fun r _ =>
      integrable_finsetSum _ (fun q _ => (samplingCharacter_integrable _).const_mul _))]
    simp_rw [integral_finsetSum _ (fun q _ => (samplingCharacter_integrable _).const_mul _),
      integral_const_mul, samplingCharacter_integral]
    simp [sub_eq_zero, -Finset.mem_range, hH.ne', samplingCharacter_zero]
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

def samplingSmooth (H : ℕ) (E : Set ℝ) (t : ℝ) : ℝ :=
  ∫ u in E, samplingKernel H (t-u) ∂unitIntervalMeasure

def samplingIntervalCoefficient (E : Set ℝ) (v : ℤ) : ℂ :=
  ∫ u in E, samplingCharacter (-v) u ∂unitIntervalMeasure

theorem samplingSmooth_bounds (H : ℕ) (hH : 0 < H) (E : Set ℝ) (t : ℝ) :
    0 ≤ samplingSmooth H E t ∧ samplingSmooth H E t ≤ 1 := by
  have hki : Integrable (fun u => samplingKernel H (t-u)) unitIntervalMeasure :=
    ((samplingKernel_continuous H).comp (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  constructor
  · exact integral_nonneg (fun u => samplingKernel_nonneg H (t-u))
  · calc
      _ ≤ ∫ u, samplingKernel H (t-u) ∂unitIntervalMeasure :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (fun u => samplingKernel_nonneg H (t-u))) hki
      _ = 1 := samplingKernel_shift_integral H hH t

theorem samplingIntervalCoefficient_zero (E : Set ℝ) :
    samplingIntervalCoefficient E 0 = ((unitIntervalMeasure E).toReal : ℂ) := by
  simp [samplingIntervalCoefficient, samplingCharacter_zero, measureReal_def]

theorem samplingIntervalCoefficient_norm (E : Set ℝ) (v : ℤ) :
    ‖samplingIntervalCoefficient E v‖ ≤ 1 := by
  unfold samplingIntervalCoefficient
  calc
    _ ≤ ∫ u in E, ‖samplingCharacter (-v) u‖ ∂unitIntervalMeasure := norm_integral_le_integral_norm _
    _ = (unitIntervalMeasure E).toReal := by simp [samplingCharacter_norm, measureReal_def]
    _ ≤ 1 := by
      have hh : unitIntervalMeasure E ≤ 1 :=
        (measure_mono (Set.subset_univ E)).trans_eq (measure_univ)
      simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hh

/-- An actual finite Fourier expansion of the smoothed interval indicator.
Keeping the two kernel indices avoids assuming a coefficient formula. -/
theorem samplingSmooth_expansion (H : ℕ) (E : Set ℝ) (t : ℝ) :
    (samplingSmooth H E t : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ q ∈ Finset.range H,
        samplingCharacter ((r : ℤ)-(q : ℤ)) t *
          samplingIntervalCoefficient E ((r : ℤ)-(q : ℤ)) := by
  rw [samplingSmooth, ← integral_complex_ofReal]
  simp_rw [samplingKernel_expansion, samplingCharacter_sub_argument]
  rw [integral_const_mul, integral_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun q _ => ((samplingCharacter_integrable _).restrict).const_mul _))]
  simp_rw [integral_finsetSum _ (fun q _ => ((samplingCharacter_integrable _).restrict).const_mul _),
    integral_const_mul]
  rfl

theorem samplingSmooth_continuous (H : ℕ) (E : Set ℝ) : Continuous (samplingSmooth H E) := by
  have hc : Continuous (fun t => (samplingSmooth H E t : ℂ)) := by
    simp_rw [samplingSmooth_expansion]
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro r hr
    apply continuous_finsetSum
    intro q hq
    exact (samplingCharacter_continuous _).mul_const _
  simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc

end
end FiniteFactor

end OAI
