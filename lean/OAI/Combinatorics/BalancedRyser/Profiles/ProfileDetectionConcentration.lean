import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Balanced.ProfileDetectionConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measureReal_deviation_le [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {r : ℝ} (hr : 0 < r) :
    μ.real {ω | r ≤ |X ω - ∫ x, X x ∂μ|} ≤ variance X μ / r ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (meas_ge_le_variance_div_sq hX hr)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg r))] at h
  exact h

omit [MeasurableSpace Ω] in

theorem small_gap_subset_deviations (X Y : Ω → ℝ) (a b ε : ℝ)
    (hgap : 2 * ε < |a - b|) :
    {ω | |X ω - Y ω| ≤ ε} ⊆
      {ω | ε / 2 ≤ |X ω - a|} ∪ {ω | ε / 2 ≤ |Y ω - b|} := by
  intro ω hω
  change ε / 2 ≤ |X ω - a| ∨ ε / 2 ≤ |Y ω - b|
  by_contra h
  push Not at h
  have h₁ := abs_sub_le a (X ω) b
  have h₂ := abs_sub_le (X ω) (Y ω) b
  rw [abs_sub_comm a (X ω)] at h₁
  change |X ω - Y ω| ≤ ε at hω
  linarith

theorem unmarked_probability_le_of_mean_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : 2 * ε < |(∫ x, X x ∂μ) - ∫ x, Y x ∂μ|) :
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
      4 * (variance X μ + variance Y μ) / ε ^ 2 := by
  have hr : 0 < ε / 2 := by positivity
  calc
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
        μ.real ({ω | ε / 2 ≤ |X ω - ∫ x, X x ∂μ|} ∪
          {ω | ε / 2 ≤ |Y ω - ∫ x, Y x ∂μ|}) :=
      measureReal_mono (small_gap_subset_deviations X Y _ _ ε hgap)
    _ ≤ μ.real {ω | ε / 2 ≤ |X ω - ∫ x, X x ∂μ|} +
        μ.real {ω | ε / 2 ≤ |Y ω - ∫ x, Y x ∂μ|} := measureReal_union_le _ _
    _ ≤ variance X μ / (ε / 2) ^ 2 + variance Y μ / (ε / 2) ^ 2 :=
      add_le_add (measureReal_deviation_le hX hr) (measureReal_deviation_le hY hr)
    _ = 4 * (variance X μ + variance Y μ) / ε ^ 2 := by ring

theorem unmarked_probability_le_of_profile_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {a b ε : ℝ} (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hXa : |(∫ x, X x ∂μ) - a| ≤ ε / 2)
    (hYb : |(∫ x, Y x ∂μ) - b| ≤ ε / 2) :
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
      4 * (variance X μ + variance Y μ) / ε ^ 2 := by
  apply unmarked_probability_le_of_mean_gap hX hY hε
  have h₁ := abs_sub_le a (∫ x, X x ∂μ) b
  have h₂ := abs_sub_le (∫ x, X x ∂μ) (∫ x, Y x ∂μ) b
  rw [abs_sub_comm a (∫ x, X x ∂μ)] at h₁
  linarith

theorem marked_probability_eq [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (ε : ℝ) :
    μ.real {ω | ε < |X ω - Y ω|} =
      1 - μ.real {ω | |X ω - Y ω| ≤ ε} := by
  have hm : NullMeasurableSet {ω | |X ω - Y ω| ≤ ε} μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hX.aestronglyMeasurable.sub hY.aestronglyMeasurable).norm.nullMeasurableSet_le
        (aestronglyMeasurable_const (b := ε))
  have hc := measureReal_compl₀ hm
  simpa only [Set.compl_ofPred, not_le, probReal_univ] using hc

theorem marked_probability_ge_of_profile_gap [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {a b ε : ℝ} (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hXa : |(∫ x, X x ∂μ) - a| ≤ ε / 2)
    (hYb : |(∫ x, Y x ∂μ) - b| ≤ ε / 2) :
    1 - 4 * (variance X μ + variance Y μ) / ε ^ 2 ≤
      μ.real {ω | ε < |X ω - Y ω|} := by
  rw [marked_probability_eq hX hY]
  exact sub_le_sub_left (unmarked_probability_le_of_profile_gap hX hY hε hgap hXa hYb) 1

theorem unmarked_probability_le_inv_order [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {a b ε C q : ℝ} (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hXa : |(∫ x, X x ∂μ) - a| ≤ ε / 2)
    (hYb : |(∫ x, Y x ∂μ) - b| ≤ ε / 2)
    (hVX : variance X μ ≤ C / q) (hVY : variance Y μ ≤ C / q) :
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤ 8 * C / (q * ε ^ 2) := by
  calc
    μ.real {ω | |X ω - Y ω| ≤ ε} ≤
      4 * (variance X μ + variance Y μ) / ε ^ 2 :=
        unmarked_probability_le_of_profile_gap hX hY hε hgap hXa hYb
    _ ≤ 4 * (C / q + C / q) / ε ^ 2 := by
      gcongr
    _ = 8 * C / (q * ε ^ 2) := by ring

section VaryingSpaces

variable {ι : Type*} {l : Filter ι} {Ωs : ι → Type*}
  [∀ i, MeasurableSpace (Ωs i)]

theorem tendsto_unmarked_probability_zero
    (μs : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (μs i)]
    (X Y : ∀ i, Ωs i → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μs i)) (hY : ∀ i, MemLp (Y i) 2 (μs i))
    (a b : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ᶠ i in l, 3 * ε < |a i - b i| ∧
      |(∫ x, X i x ∂(μs i)) - a i| ≤ ε / 2 ∧
      |(∫ x, Y i x ∂(μs i)) - b i| ≤ ε / 2)
    (hvar : Tendsto (fun i => variance (X i) (μs i) + variance (Y i) (μs i))
      l (𝓝 0)) :
    Tendsto (fun i => (μs i).real {ω | |X i ω - Y i ω| ≤ ε}) l (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
  · filter_upwards [hgood] with i hi
    exact unmarked_probability_le_of_profile_gap (hX i) (hY i) hε hi.1 hi.2.1 hi.2.2
  · simpa only [mul_zero, zero_div] using (hvar.const_mul 4).div_const (ε ^ 2)

theorem tendsto_marked_probability_one
    (μs : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (μs i)]
    (X Y : ∀ i, Ωs i → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μs i)) (hY : ∀ i, MemLp (Y i) 2 (μs i))
    (a b : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ᶠ i in l, 3 * ε < |a i - b i| ∧
      |(∫ x, X i x ∂(μs i)) - a i| ≤ ε / 2 ∧
      |(∫ x, Y i x ∂(μs i)) - b i| ≤ ε / 2)
    (hvar : Tendsto (fun i => variance (X i) (μs i) + variance (Y i) (μs i))
      l (𝓝 0)) :
    Tendsto (fun i => (μs i).real {ω | ε < |X i ω - Y i ω|}) l (𝓝 1) := by
  have hz := tendsto_unmarked_probability_zero μs X Y hX hY a b hε hgood hvar
  have hc := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  simp only [sub_zero] at hc
  convert hc using 1
  funext i
  exact marked_probability_eq (hX i) (hY i) ε

end VaryingSpaces

section FiniteAveraging

variable {ι : Type*} {Ωs : ι → Type*} [∀ i, MeasurableSpace (Ωs i)]

theorem weighted_detection_le_marked_add_variance
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (μs : ∀ i, Measure (Ωs i)) [∀ i, IsProbabilityMeasure (μs i)]
    (X Y : ∀ i, Ωs i → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μs i)) (hY : ∀ i, MemLp (Y i) 2 (μs i))
    (a b : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hXa : ∀ i ∈ s, |(∫ x, X i x ∂(μs i)) - a i| ≤ ε / 2)
    (hYb : ∀ i ∈ s, |(∫ x, Y i x ∂(μs i)) - b i| ≤ ε / 2) :
    (∑ i ∈ s, if 3 * ε < |a i - b i| then w i else 0) ≤
      (∑ i ∈ s, w i * (μs i).real {ω | ε < |X i ω - Y i ω|}) +
      ∑ i ∈ s, w i * (4 * (variance (X i) (μs i) + variance (Y i) (μs i)) / ε ^ 2) := by
  classical
  calc
    (∑ i ∈ s, if 3 * ε < |a i - b i| then w i else 0) ≤
        ∑ i ∈ s, w i * ((μs i).real {ω | ε < |X i ω - Y i ω|} +
          4 * (variance (X i) (μs i) + variance (Y i) (μs i)) / ε ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hsep : 3 * ε < |a i - b i|
      · simp only [ite_eq_left hsep]
        have hb := marked_probability_ge_of_profile_gap (hX i) (hY i) hε hsep
          (hXa i hi) (hYb i hi)
        have hb' : 1 ≤ (μs i).real {ω | ε < |X i ω - Y i ω|} +
            4 * (variance (X i) (μs i) + variance (Y i) (μs i)) / ε ^ 2 := by
          linarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hb' (hw i hi)
      · simp only [ite_eq_right hsep]
        have hV : 0 ≤ variance (X i) (μs i) + variance (Y i) (μs i) :=
          add_nonneg (variance_nonneg _ _) (variance_nonneg _ _)
        exact mul_nonneg (hw i hi) (add_nonneg measureReal_nonneg
          (div_nonneg (mul_nonneg (by norm_num) hV) (sq_nonneg ε)))
    _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]

end FiniteAveraging

end Balanced.ProfileDetectionConcentration

end OAI
