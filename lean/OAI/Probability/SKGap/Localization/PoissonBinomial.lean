import Mathlib
import OAI.Probability.SKGap.Localization.SumPoissonMass
import OAI.Probability.SKGap.Gaussian.GaussianPDFMoment
import OAI.Probability.SKGap.Localization.IntegrableMulBounded

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

theorem poisson_to_binomial {q B : ℝ} (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (a : ℕ → ℕ → ℝ)
    (hab : ∀ n j, |a n j| ≤ B)
    (hp : ∀ y : ℝ, Tendsto (fun n => ∑' j,
      poissonMass (q*M n+y*Real.sqrt (M n)) j*a n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, binomialMass q (M n) j*a n j) atTop (𝓝 0) := by
  let u : ℕ → ℝ → ℝ := fun n => testHistogram q (M n) (a n)
  have hu (n : ℕ) : AEStronglyMeasurable (u n) :=
    (measurable_testHistogram q (M n) (a n)).aestronglyMeasurable
  have hub (n : ℕ) (x : ℝ) : |u n x| ≤ B := testHistogram_bound hB.le (hab n) q (M n) x
  have hMn : ∀ᶠ n in atTop, 0 < M n := hM.eventually (eventually_gt_atTop 0)
  have hPi (y : ℝ) : ∀ᶠ n in atTop,
      Integrable (histogram q (M n) (poissonMass (q*M n+y*Real.sqrt (M n)))) := by
    filter_upwards [hMn] with n hn
    exact integrable_histogram (hasSum_poissonMass _) q hn
  have hdiff (y : ℝ) := pairing_of_L1_limit (hPi y)
    (integrable_gaussianPDFReal y ⟨q,hq.le⟩) hu hub ((poisson_density_L1 hq y).comp hM)
  have hP (y : ℝ) : Tendsto (fun n => ∫ x : ℝ,
      histogram q (M n) (poissonMass (q*M n+y*Real.sqrt (M n))) x*u n x)
      atTop (𝓝 0) := by
    apply (hp y).congr'
    filter_upwards [hMn] with n hn
    exact (integral_histogram_test (hasSum_poissonMass _).summable (hab n) q hn).symm
  have hG (y : ℝ) : Tendsto (fun n => ∫ x : ℝ, gaussianPDFReal y ⟨q,hq.le⟩ x*u n x)
      atTop (𝓝 0) := by
    have hh := (hP y).sub (hdiff y)
    simpa only [sub_sub_cancel,sub_zero] using hh
  let v : ℝ≥0 := ⟨q,hq.le⟩
  let w : ℝ≥0 := ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩
  have hv : 0 < v := hq
  have hw : 0 < w := mul_pos hq (by linarith)
  have hwv : w ≤ v := by
    change q*(1-q) ≤ q
    nlinarith [sq_nonneg q]
  have hGb : Tendsto (fun n => ∫ x : ℝ, gaussianPDFReal 0 w x*u n x)
      atTop (𝓝 0) :=
    pairing_of_finite_approximation (integrable_gaussianPDFReal 0 w)
      (fun y => integrable_gaussianPDFReal (-y) v) hB hu hub
      (fun ε hε => finite_gaussianPDF_approximation hv hw hwv hε) (fun y => hG (-y))
  have hBi : ∀ᶠ n in atTop, Integrable (histogram q (M n) (binomialMass q (M n))) := by
    filter_upwards [hMn] with n hn
    exact integrable_histogram (hasSum_binomialMass q _) q hn
  have hBd := pairing_of_L1_limit hBi (integrable_gaussianPDFReal 0 w) hu hub
    ((binomial_density_L1 hq hq1).comp hM)
  have hBin : Tendsto (fun n => ∫ x : ℝ,
      histogram q (M n) (binomialMass q (M n)) x*u n x) atTop (𝓝 0) := by
    have hh := hBd.add hGb
    simpa only [sub_add_cancel,zero_add] using hh
  apply hBin.congr'
  filter_upwards [hMn] with n hn
  exact integral_histogram_test (hasSum_binomialMass q _).summable (hab n) q hn

lemma uniform_zero_of_selections {ι : ℕ → Type*} [∀ n, Nonempty (ι n)]
    (f : (n : ℕ) → ι n → ℝ)
    (hf : ∀ i : (n : ℕ) → ι n, Tendsto (fun n => f n (i n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n, |f n i| < ε := by
  classical
  intro ε hε
  let i : (n : ℕ) → ι n := fun n =>
    if h : ∃ i : ι n, ε ≤ |f n i| then Classical.choose h else Classical.choice (inferInstance : Nonempty (ι n))
  have hh : ∀ᶠ n in atTop, |f n (i n)| < ε := by
    have he := (hf i).eventually (Metric.ball_mem_nhds 0 hε)
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he
  filter_upwards [hh] with n hn
  intro j
  by_contra h
  have hbad : ∃ j : ι n, ε ≤ |f n j| := ⟨j,le_of_not_gt h⟩
  have hlarge : ε ≤ |f n (i n)| := by simpa only [i,dite_eq_left hbad] using Classical.choose_spec hbad
  exact (not_le.mpr hn) hlarge

theorem poisson_to_binomial_uniform {q B : ℝ} (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {ι : ℕ → Type*} [∀ n, Nonempty (ι n)]
    (a : (n : ℕ) → ι n → ℕ → ℝ) (hab : ∀ n i j, |a n i j| ≤ B)
    (hp : ∀ y ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, poissonMass (q*M n+y*Real.sqrt (M n)) j*a n i j| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, binomialMass q (M n) j*a n i j| < ε := by
  apply uniform_zero_of_selections
  intro i
  apply poisson_to_binomial hq hq1 hB M hM (fun n => a n (i n))
    (fun n j => hab n (i n) j)
  intro y
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp y ε hε)
  refine ⟨N,fun n hn => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using hN n hn (i n)

theorem poisson_to_binomial_bounded {q B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (a : ℕ → ℕ → ℝ)
    (hab : ∀ n j, |a n j| ≤ B)
    (hp : ∀ y : ℝ, Tendsto (fun n => ∑' j,
      poissonMass (q*M n+y*Real.sqrt (M n)) j*a n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, binomialMass q (M n) j*a n j) atTop (𝓝 0) := by
  apply poisson_to_binomial hq hq1 (show 0 < |B|+1 by positivity) M hM a
    (fun n j => (hab n j).trans ((le_abs_self B).trans (by linarith))) hp

theorem poisson_to_binomial_uniform_clocks {q B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {ι : ℕ → Type*} [∀ n, Nonempty (ι n)] (M : (n : ℕ) → ι n → ℕ)
    (hM : ∀ K : ℕ, ∀ᶠ n in atTop, ∀ i : ι n, K ≤ M n i)
    (a : (n : ℕ) → ι n → ℕ → ℝ) (hab : ∀ n i j, |a n i j| ≤ B)
    (hp : ∀ y ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, poissonMass (q*M n i+y*Real.sqrt (M n i)) j*a n i j| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, binomialMass q (M n i) j*a n i j| < ε := by
  apply uniform_zero_of_selections
  intro i
  have hMi : Tendsto (fun n => M n (i n)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro K
    filter_upwards [hM K] with n hn
    exact hn (i n)
  apply poisson_to_binomial_bounded hq hq1 (fun n => M n (i n)) hMi (fun n => a n (i n))
    (fun n j => hab n (i n) j)
  intro y
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp y ε hε)
  refine ⟨N,fun n hn => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using hN n hn (i n)

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
