import Mathlib
import OAI.Probability.SKGap.Localization.LogQuadratic
import OAI.Probability.SKGap.Localization.StepMass

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
namespace SKGapCutoff.Clock

lemma hasSum_poissonMass (m : ℝ) : HasSum (poissonMass m) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp m).mul_left (Real.exp (-m)) using 1
  · ext n
    simp only [poissonMass,mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

lemma hasSum_binomialMass (q : ℝ) (n : ℕ) : HasSum (binomialMass q n) 1 := by
  have hh : HasSum (binomialMass q n)
      (∑ k ∈ Finset.range (n+1), binomialMass q n k) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range (n+1))
    (f := binomialMass q n) (by
      intro k hk
      have hnk : n < k := by simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hk
      simp only [binomialMass,Nat.choose_eq_zero_of_lt hnk,Nat.cast_zero,zero_mul])
  convert! hh using 1
  have hb := add_pow q (1-q) n
  have hq : q+(1-q)=1 := by ring
  rw [hq,one_pow] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [binomialMass]
  ring

lemma poisson_density_pointwise {q : ℝ} (hq : 0 < q) (y x : ℝ) :
    Tendsto (fun n : ℕ => histogram q n (poissonMass (q*n+y*Real.sqrt n)) x)
      atTop (𝓝 (gaussianPDFReal y ⟨q,hq.le⟩ x)) := by
  have hh := poisson_histogram_pointwise hq x y
  rw [gaussian_formula hq x y] at hh
  apply hh.congr'
  filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0)] with n hn
  simp only [histogram,stepMass_of_nonneg _ hn,centralIndex]

lemma binomial_density_pointwise {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => histogram q n (binomialMass q n) x)
      atTop (𝓝 (gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x)) := by
  apply (binomial_histogram_pointwise hql hqu x).congr'
  filter_upwards [(center_tendsto_atTop hql x).eventually (eventually_ge_atTop 0)] with n hn
  simp only [histogram,stepMass_of_nonneg _ hn,centralIndex]

theorem poisson_density_L1 {q : ℝ} (hq : 0 < q) (y : ℝ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |histogram q n (poissonMass (q*n+y*Real.sqrt n)) x-
        gaussianPDFReal y ⟨q,hq.le⟩ x|) atTop (𝓝 0) := by
  apply scheffe_density_filter
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact integrable_histogram (hasSum_poissonMass _) q hn
  · exact integrable_gaussianPDFReal _ _
  · filter_upwards [(center_tendsto_atTop hq y).eventually (eventually_ge_atTop 0)] with n hn
    exact Filter.Eventually.of_forall (histogram_nonneg (fun j => by
      unfold poissonMass
      positivity) q n)
  · exact Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _)
  · exact Filter.Eventually.of_forall (poisson_density_pointwise hq y)
  · have hv : (⟨q,hq.le⟩ : ℝ≥0) ≠ 0 := by
      intro h
      have hh := congrArg (fun r : ℝ≥0 => (r:ℝ)) h
      exact hq.ne' hh
    rw [integral_gaussianPDFReal_eq_one _ hv]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (integral_histogram (hasSum_poissonMass _) q hn).symm

theorem binomial_density_L1 {q : ℝ} (hql : 0 < q) (hqu : q < 1) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |histogram q n (binomialMass q n) x-
        gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x|) atTop (𝓝 0) := by
  apply scheffe_density_filter
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact integrable_histogram (hasSum_binomialMass q n) q hn
  · exact integrable_gaussianPDFReal _ _
  · apply Filter.Eventually.of_forall
    intro n
    exact Filter.Eventually.of_forall (histogram_nonneg (fun j => by
      unfold binomialMass
      positivity) q n)
  · exact Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _)
  · exact Filter.Eventually.of_forall (binomial_density_pointwise hql hqu)
  · have hv : (⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ : ℝ≥0) ≠ 0 := by
      intro h
      have hh := congrArg (fun r : ℝ≥0 => (r:ℝ)) h
      exact (mul_pos hql (by linarith : 0 < 1-q)).ne' hh
    rw [integral_gaussianPDFReal_eq_one _ hv]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (integral_histogram (hasSum_binomialMass q n) q hn).symm

end SKGapCutoff.Clock

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

end

end OAI
