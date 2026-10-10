import OAI.Analysis.CircleDomains.LengthArea
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-!
# Weighted dust incidence

This is the dust part of `eq:weighted-level-bound` in Section 1 of
`047-02`. A point contributes its weight on a measurable set of levels.
Tonelli converts the expected total incidence to the sum of weights
times level probabilities; the band-incidence estimate bounds these
probabilities, and square summability makes the result finite.
-/

open Set MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def weightedBandIncidence {T ι : Type*}
    (E : ι → Set T) (m : ι → ℝ) (t : T) : ℝ≥0∞ :=
  ∑' s, (E s).indicator (fun _ => ENNReal.ofReal (m s)) t

theorem measurable_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    Measurable (weightedBandIncidence E m) :=
  Measurable.tsum (fun s => measurable_const.indicator (hE s))

theorem weightedBandIncidence_toReal_eq {T ι : Type*}
    (E : ι → Set T) (m : ι → ℝ) (hm : ∀ s, 0 ≤ m s) (t : T) :
    (weightedBandIncidence E m t).toReal = ∑' s, (E s).indicator (fun _ => m s) t := by
  classical
  rw [weightedBandIncidence, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro s
    by_cases ht : t ∈ E s
    · simp only [indicator_of_mem ht, ENNReal.toReal_ofReal (hm s)]
    · simp only [indicator_of_notMem ht, ENNReal.toReal_zero]
  · intro s
    by_cases ht : t ∈ E s
    · simpa only [indicator_of_mem ht] using ENNReal.ofReal_ne_top
    · simp only [indicator_of_notMem ht, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]

/-- Tonelli's exact incidence identity. -/
theorem lintegral_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν = ∑' s, ENNReal.ofReal (m s) * ν (E s) := by
  unfold weightedBandIncidence
  rw [lintegral_tsum]
  · apply tsum_congr
    intro s
    exact lintegral_indicator_const (hE s) _
  · intro s
    exact (measurable_const.indicator (hE s)).aemeasurable

/-- The band probability bound yields the weighted-level dust estimate. -/
theorem lintegral_weightedBandIncidence_le {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν ≤ ENNReal.ofReal (∑' s, m s * a s) := by
  rw [lintegral_weightedBandIncidence ν E m hE]
  have hs := LengthArea.summable_mul_of_squares hm2 ha2
  have hnonneg (s) : 0 ≤ m s * a s := mul_nonneg (hm s) (ha s)
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hs]
  apply ENNReal.tsum_le_tsum
  intro s
  rw [ENNReal.ofReal_mul (hm s)]
  exact mul_le_mul_right (hband s) _

/-- The Cauchy--Schwarz bound for the weighted band series. -/
theorem tsum_mul_le_sqrt_square_sums {ι : Type*} (m a : ι → ℝ)
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    (∑' s, m s * a s) ≤ Real.sqrt (∑' s, m s ^ 2) * Real.sqrt (∑' s, a s ^ 2) := by
  apply hasSum_le_of_sum_le (LengthArea.summable_mul_of_squares hm2 ha2).hasSum
  intro F
  apply (Real.sum_mul_le_sqrt_mul_sqrt F m a).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (hm2.sum_le_tsum F (fun s _ => sq_nonneg (m s))))
    (Real.sqrt_le_sqrt (ha2.sum_le_tsum F (fun s _ => sq_nonneg (a s))))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem lintegral_weightedBandIncidence_lt_top
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν < ∞ :=
  (lintegral_weightedBandIncidence_le ν E m a hE hm ha hband hm2 ha2).trans_lt
    ENNReal.ofReal_lt_top

/-- The weighted series is summable at almost every level. -/
theorem ae_summable_weighted_band_series
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∀ᵐ t ∂ν, Summable (fun s => (E s).indicator (fun _ => m s) t) := by
  have hfinite := lintegral_weightedBandIncidence_lt_top ν E m a hE hm ha hband hm2 ha2
  filter_upwards [ae_lt_top (measurable_weightedBandIncidence E m hE) hfinite.ne] with t ht
  change (∑' s, (E s).indicator (fun _ => ENNReal.ofReal (m s)) t) < ∞ at ht
  apply (ENNReal.summable_toReal ht.ne).congr
  intro s
  by_cases hts : t ∈ E s
  · simp only [indicator_of_mem hts, ENNReal.toReal_ofReal (hm s)]
  · simp only [indicator_of_notMem hts, ENNReal.toReal_zero]

theorem lintegral_weightedBandIncidence_le_cauchySchwarz
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν ≤
      ENNReal.ofReal (Real.sqrt (∑' s, m s ^ 2) * Real.sqrt (∑' s, a s ^ 2)) :=
  (lintegral_weightedBandIncidence_le ν E m a hE hm ha hband hm2 ha2).trans
    (ENNReal.ofReal_le_ofReal (tsum_mul_le_sqrt_square_sums m a hm2 ha2))

/-- The same bound as an ordinary real integral; the integrand is finite
almost everywhere by its finite Tonelli integral. -/
theorem integral_weightedBandIncidence_toReal_le
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    Integrable (fun t => (weightedBandIncidence E m t).toReal) ν ∧
      (∫ t, (weightedBandIncidence E m t).toReal ∂ν) ≤ ∑' s, m s * a s := by
  have hmeas := measurable_weightedBandIncidence E m hE
  have hfinite := lintegral_weightedBandIncidence_lt_top ν E m a hE hm ha hband hm2 ha2
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfinite.ne, ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinite.ne)]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_weightedBandIncidence_le ν E m a hE hm ha hband hm2 ha2)
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg (fun s => mul_nonneg (hm s) (ha s)))]
    using hb

/-- The paper's ordinary real weighted series is integrable and obeys
the same dust contribution bound. -/
theorem integral_weighted_band_series_le
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    Integrable (fun t => ∑' s, (E s).indicator (fun _ => m s) t) ν ∧
      (∫ t, ∑' s, (E s).indicator (fun _ => m s) t ∂ν) ≤ ∑' s, m s * a s := by
  simpa only [weightedBandIncidence_toReal_eq E m hm] using
    integral_weightedBandIncidence_toReal_le ν E m a hE hm ha hband hm2 ha2

end CircleDomainRigidity

end OAI
