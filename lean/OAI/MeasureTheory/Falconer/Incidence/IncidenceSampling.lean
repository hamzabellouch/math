import OAI.MeasureTheory.Falconer.Estimates.IidSampling

namespace OAI

/-!
# Incidence retained by the sampled labels

The first sample must preserve incidence as well as its direction counts.
The retained point set then consists of points with many incident sampled
labels. These assertions concern the original label spaces.
-/

namespace Falconer
open Set MeasureTheory

/-- At least a quarter of the incidence remains on the points whose
empirical incidence is at least a quarter. -/
theorem high_value_set_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I / 2 ≤ ∫ x, f x ∂μ) :
    I / 4 ≤ μ.real {x | I / 4 ≤ f x} := by
  classical
  let G := {x | I / 4 ≤ f x}
  have hG : MeasurableSet G := measurableSet_le measurable_const hf
  have hpoint : ∀ x, f x ≤ I / 4 + G.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ G
    · simp only [indicator_of_mem hx]
      linarith [hf1 x]
    · simp only [indicator_of_notMem hx, add_zero]
      exact (lt_of_not_ge hx).le
  have hb : (∫ x, f x ∂μ) ≤ I / 4 + μ.real G := by
    calc
      _ ≤ ∫ x, I / 4 + G.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        integral_mono hfi ((integrable_const _).add ((integrable_const 1).indicator hG)) hpoint
      _ = _ := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hG),
          integral_indicator_const (1 : ℝ) hG]
        simp
  change I / 4 ≤ μ.real G
  linarith

theorem integral_empirical_kernel {X W : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → W → ℝ) (hF : ∀ w, Integrable (fun x => F x w) μ)
    {n : ℕ} (ω : Fin n → W) :
    (∫ x, iidAverage (F x) ω ∂μ) = iidAverage (fun w => ∫ x, F x w ∂μ) ω := by
  simp only [iidAverage]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hF (ω i))]

/-- A direction sample can simultaneously satisfy the prescribed cell
counts and leave a point set of mass at least `I/4` with empirical
incidence at least `I/4`. No coordinates of the labels are identified. -/
theorem exists_incidence_sample {X W κ : Type*}
    [MeasurableSpace X] [MeasurableSpace W] [DecidableEq κ]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
    (F : X → W → ℝ) (hF : Measurable (Function.uncurry F))
    (hF0 : ∀ x w, 0 ≤ F x w) (hF1 : ∀ x w, F x w ≤ 1)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set W)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure W).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (Real.exp 1 - 1) * p j + L ≤ T j)
    {I : ℝ} (hI : 0 < I)
    (hmean : I ≤ ∫ w, ∫ x, F x w ∂(μ : Measure X) ∂(ν : Measure W))
    (hsmall : (B.card : ℝ) * Real.exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → W,
      (∀ j ∈ B, iidCount (A j) ω < T j) ∧
      I / 4 ≤ (μ : Measure X).real {x | I / 4 ≤ iidAverage (F x) ω} := by
  have hFx (w : W) : Measurable (fun x => F x w) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hFi (w : W) : Integrable (fun x => F x w) (μ : Measure X) := by
    apply Integrable.of_bound (hFx w).aestronglyMeasurable 1
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x w)] using hF1 x w
  have hIntegral : Measurable (fun w => ∫ x, F x w ∂(μ : Measure X)) :=
    hF.stronglyMeasurable.integral_prod_left.measurable
  have hIntegral0 (w : W) : 0 ≤ ∫ x, F x w ∂(μ : Measure X) :=
    integral_nonneg (fun x => hF0 x w)
  have hIntegral1 (w : W) : (∫ x, F x w ∂(μ : Measure X)) ≤ 1 := by
    have hh := integral_mono (hFi w) (integrable_const (1 : ℝ)) (fun x => hF1 x w)
    simpa using hh
  have hIntegrable : Integrable (fun w => ∫ x, F x w ∂(μ : Measure X)) (ν : Measure W) := by
    apply Integrable.of_bound hIntegral.aestronglyMeasurable 1
    filter_upwards with w
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hIntegral0 w)] using hIntegral1 w
  obtain ⟨ω, hcounts, hmass⟩ := exists_iid_sample_with_counts_and_incidence ν hn B A hA p T L
    hp hprob hT (fun w => ∫ x, F x w ∂(μ : Measure X)) hIntegrable hIntegral1 hI hmean hsmall
  refine ⟨ω, hcounts, ?_⟩
  apply high_value_set_mass (μ : Measure X) (fun x => iidAverage (F x) ω)
  · unfold iidAverage
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hFx (ω i)))
  · unfold iidAverage
    exact (integrable_finsetSum _ (fun i _ => hFi (ω i))).const_mul _
  · intro x
    exact iidAverage_le_one (F x) (hF1 x) hn ω
  · exact hI
  · simpa only [integral_empirical_kernel (μ : Measure X) F hFi ω] using hmass

end Falconer

end OAI
