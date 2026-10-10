import Mathlib.Probability.Moments.Basic

namespace OAI

/-!
# Exponential tails for sampled incidence counts

The sample-count estimate in `ang:planar-measures` needs an exponential
tail even when the expected count is bounded. Applying Chernoff at the
fixed parameter one gives a sufficient bound without an asymptotic
binomial formula.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

private theorem exp_indicator_one {Ω : Type*} (A : Set Ω) (ω : Ω) :
    exp (A.indicator (fun _ => (1 : ℝ)) ω) =
      1 + (exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases h : ω ∈ A <;> simp [h]

/-- The exponential moment of a Bernoulli indicator at parameter one. -/
theorem indicator_mgf_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    mgf (A.indicator (fun _ => (1 : ℝ))) μ 1 = 1 + (exp 1 - 1) * μ.real A := by
  classical
  have hI : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  simp only [mgf, one_mul, exp_indicator_one]
  rw [integral_add (integrable_const 1) (hI.const_mul (exp 1 - 1)),
    integral_const_mul, integral_indicator_const (1 : ℝ) hA]
  simp

/-- The tail bound retains the actual small mean of each indicator. -/
theorem independent_indicator_sum_tail {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T : ℝ} (_hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p) :
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
  classical
  let X : ι → Ω → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hmeas : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hint : ∀ i ∈ S, Integrable (fun ω => exp (1 * X i ω)) μ := by
    intro i _
    apply integrable_exp_mul_of_le 1 1 (by norm_num) (hmeas i).aemeasurable
    exact ae_of_all _ fun ω => by
      by_cases h : ω ∈ A i <;> simp [X, h]
  have hsumint := hindep.integrable_exp_mul_sum hmeas hint
  have hexp : 0 ≤ exp 1 - 1 := by
    have := exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
    rw [exp_zero] at this
    linarith
  have hbound : ∀ i ∈ S, mgf (X i) μ 1 ≤ exp ((exp 1 - 1) * p) := by
    intro i hi
    rw [indicator_mgf_one μ (A i) (hA i)]
    calc
      1 + (exp 1 - 1) * μ.real (A i) ≤ 1 + (exp 1 - 1) * p := by
        gcongr
        exact hprob i hi
      _ ≤ exp ((exp 1 - 1) * p) := by simpa [add_comm] using add_one_le_exp ((exp 1 - 1) * p)
  have hprod : mgf (∑ i ∈ S, X i) μ 1 ≤ exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
    rw [hindep.mgf_sum hmeas]
    calc
      ∏ i ∈ S, mgf (X i) μ 1 ≤ ∏ _i ∈ S, exp ((exp 1 - 1) * p) :=
        Finset.prod_le_prod₀ (fun _ _ => mgf_nonneg) hbound
      _ = exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
        rw [← exp_sum]
        simp [mul_assoc]
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ S, X i) T
    (show (0 : ℝ) ≤ 1 by norm_num) hsumint
  calc
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
        exp (-1 * T) * mgf (∑ i ∈ S, X i) μ 1 := by
      simpa only [Finset.sum_apply, X] using htail
    _ ≤ exp (-1 * T) * exp ((S.card : ℝ) * (exp 1 - 1) * p) :=
      mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
      rw [← exp_add]
      congr 1
      ring

/-- A threshold exceeding the exponential-moment mean by `L` fails with
probability at most `exp (-L)`. -/
theorem independent_indicator_sum_tail_le {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T L : ℝ} (hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p)
    (hT : (S.card : ℝ) * (exp 1 - 1) * p + L ≤ T) :
    μ {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      ENNReal.ofReal (exp (-L)) := by
  have h := (independent_indicator_sum_tail μ A hA hindep S hp hprob).trans
    (exp_le_exp.mpr (by linarith : (S.card : ℝ) * (exp 1 - 1) * p - T ≤ -L))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Simultaneous sample-count bounds over any fixed finite collection of
cells. Independence is required only among the draws for each cell. -/
theorem finite_sample_count_failure {Ω ι κ : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Finset κ) (S : Finset ι) (A : κ → ι → Set Ω)
    (hA : ∀ j i, MeasurableSet (A j i))
    (hindep : ∀ j ∈ B,
      iIndepFun (fun i => (A j i).indicator (fun _ => (1 : ℝ))) μ)
    (p T : κ → ℝ) (L : ℝ) (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, ∀ i ∈ S, μ.real (A j i) ≤ p j)
    (hT : ∀ j ∈ B, (S.card : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    μ (⋃ j ∈ B, {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  calc
    _ ≤ ∑ j ∈ B,
        μ {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ B, ENNReal.ofReal (exp (-L)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact independent_indicator_sum_tail_le μ (A j) (hA j) (hindep j hj) S
        (hp j hj) (hprob j hj) (hT j hj)
    _ = _ := by simp [ENNReal.ofReal_mul, Nat.cast_nonneg]

/-- A small exceptional family of samples cannot carry all the expected
incidence. This is the probabilistic-method selection used after the
simultaneous count bound. -/
theorem exists_good_sample_incidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℝ) (hJ : Integrable J μ)
    (hJone : ∀ ω, J ω ≤ 1) (B : Set Ω) (hB : MeasurableSet B)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ ω, J ω ∂μ)
    (hbad : μ.real B ≤ I / 4) :
    ∃ ω ∉ B, I / 2 ≤ J ω := by
  classical
  by_contra h
  push Not at h
  have hpoint : ∀ ω, J ω ≤ I / 2 + B.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · simp only [indicator_of_mem hω]
      linarith [hJone ω]
    · simp only [indicator_of_notMem hω, add_zero]
      exact (h ω hω).le
  have hbound : (∫ ω, J ω ∂μ) ≤ I / 2 + μ.real B := by
    calc
      (∫ ω, J ω ∂μ) ≤ ∫ ω, I / 2 + B.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_mono hJ ((integrable_const _).add ((integrable_const 1).indicator hB)) hpoint
      _ = _ := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hB),
          integral_indicator_const (1 : ℝ) hB]
        simp
  linarith

end Falconer

end OAI
