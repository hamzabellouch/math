import OAI.Analysis.FiniteFactor.Sampling.Kernel

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

theorem samplingCharacter_nat (r : ℕ) (t : ℝ) :
    samplingCharacter (r : ℤ) t = samplingCharacter 1 t ^ r := by
  induction r with
  | zero => simp [samplingCharacter_zero]
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, samplingCharacter_add, ih, pow_succ]

/-- Geometric-sum cancellation controls the kernel away from the origin. -/
theorem samplingKernel_geometric_bound (H : ℕ) (t : ℝ) :
    ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖ *
      ‖samplingCharacter 1 t - 1‖ ≤ 2 := by
  simp_rw [samplingCharacter_nat]
  rw [← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖samplingCharacter 1 t ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by norm_num [norm_pow, samplingCharacter_norm]

/-- Elementary chord lower bound, including both halves of the unit interval. -/
theorem samplingCharacter_chord_lower (δ t : ℝ) (hδ : 0 ≤ δ)
    (ht : δ ≤ t) (ht' : t ≤ 1-δ) :
    4*δ ≤ ‖samplingCharacter 1 t-1‖ := by
  have he : samplingCharacter 1 t = Complex.exp (Complex.I * ((2*Real.pi*t : ℝ) : ℂ)) := by
    unfold samplingCharacter
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have harg : 2*Real.pi*t/2 = Real.pi*t := by ring
  rw [harg, Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  have hsin : 2*δ ≤ Real.sin (Real.pi*t) := by
    by_cases hhalf : t ≤ 1/2
    · have ht0 : 0 ≤ t := hδ.trans ht
      have hh := Real.mul_le_sin (x := Real.pi*t) (by positivity)
        (by nlinarith [Real.pi_pos])
      have he : 2/Real.pi*(Real.pi*t) = 2*t := by field_simp
      rw [he] at hh
      linarith
    · have ht0 : 0 ≤ 1-t := by linarith
      have hh := Real.mul_le_sin (x := Real.pi*(1-t)) (by positivity)
        (by nlinarith [Real.pi_pos])
      have he : 2/Real.pi*(Real.pi*(1-t)) = 2*(1-t) := by field_simp
      rw [he, show Real.pi*(1-t) = Real.pi-Real.pi*t by ring, Real.sin_pi_sub] at hh
      linarith
  have := le_abs_self (Real.sin (Real.pi*t))
  linarith

theorem samplingKernel_tail_bound (H : ℕ) (hH : 0 < H) (δ t : ℝ)
    (hδ : 0 < δ) (ht : δ ≤ t) (ht' : t ≤ 1-δ) :
    samplingKernel H t ≤ 1/(4*(H : ℝ)*δ^2) := by
  have hc := samplingCharacter_chord_lower δ t hδ.le ht ht'
  have hg := samplingKernel_geometric_bound H t
  let A := ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖
  have hA : 0 ≤ A := norm_nonneg _
  have hbound : A ≤ 1/(2*δ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*δ)).mpr
    have hh := mul_le_mul_of_nonneg_left hc hA
    dsimp [A] at *
    nlinarith
  have hsq := pow_le_pow_left₀ hA hbound 2
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold samplingKernel
  calc
    _ ≤ (1/(2*δ))^2/(H : ℝ) := div_le_div_of_nonneg_right hsq hHR.le
    _ = _ := by ring

/-- Actual mass of the part of the Fejer kernel outside a delta-neighborhood
of the integer cut. -/
theorem samplingKernel_tail_integral (H : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in Set.Icc δ (1-δ), samplingKernel H t ∂unitIntervalMeasure) ≤
      1/(4*(H : ℝ)*δ^2) := by
  have hki : Integrable (samplingKernel H) unitIntervalMeasure :=
    (samplingKernel_continuous H).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  rw [← integral_indicator measurableSet_Icc]
  have hle : ∀ t, (Set.Icc δ (1-δ)).indicator (samplingKernel H) t ≤ 1/(4*(H : ℝ)*δ^2) := by
    intro t
    by_cases ht : t ∈ Set.Icc δ (1-δ)
    · rw [Set.indicator_of_mem ht]
      exact samplingKernel_tail_bound H hH δ t hδ ht.1 ht.2
    · rw [Set.indicator_of_notMem ht]
      positivity
  have hh := integral_mono_ae (hki.indicator measurableSet_Icc) (integrable_const (1/(4*(H : ℝ)*δ^2)))
    (Filter.Eventually.of_forall hle)
  simpa using hh

end
end FiniteFactor

end OAI
