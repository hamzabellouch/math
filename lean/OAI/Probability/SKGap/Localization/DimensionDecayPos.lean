import Mathlib
import OAI.Probability.SKGap.Localization.DimensionDecay

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
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
namespace SKGapCutoff

lemma dimensionDecay_pos (a : ℝ) (n : ℕ) : 0 < dimensionDecay a n := Real.exp_pos _

lemma dimensionDecay_le_one {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    dimensionDecay a n ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
  nlinarith

lemma dimensionDecay_mul (a b : ℝ) (n : ℕ) :
    dimensionDecay a n * dimensionDecay b n = dimensionDecay (a+b) n := by
  unfold dimensionDecay
  rw [← Real.exp_add]
  congr 1
  ring

lemma nat_mul_dimensionDecay {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n:ℝ)*dimensionDecay a n = dimensionDecay (a-1) n := by
  simpa only [show 1+(a-1) = a by ring, dimensionDecay] using mul_exp_log_identity hn (a-1)

lemma nat_sq_mul_dimensionDecay {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n:ℝ)^2*dimensionDecay a n = dimensionDecay (a-2) n := by
  rw [pow_two, mul_assoc, nat_mul_dimensionDecay hn, nat_mul_dimensionDecay hn]
  congr 1
  ring

lemma exp_cutoffTime_eq_dimensionDecay {rate : ℝ} (hrate : rate ≠ 0) (ρ c : ℝ) (n : ℕ) :
    Real.exp (-2*ρ*(c*cutoffTime rate n)) = dimensionDecay (c*ρ/rate) n := by
  unfold cutoffTime dimensionDecay
  congr 1
  field_simp [hrate]

lemma dimensionDecay_mul_cutoffTime_tendsto {q rate : ℝ} (hq : 0 < q) :
    Tendsto (fun n => dimensionDecay q n*cutoffTime rate n) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 q hq).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simp only [Function.comp_def, Real.rpow_one] at hh
  have hh' := hh.div_const (2*rate)
  convert hh' using 1
  · funext n
    unfold dimensionDecay cutoffTime
    ring
  · simp

lemma linear_mean_error_tendsto {C α q : ℝ} (hα : 1 < α) (hq : 1 < q) :
    Tendsto (fun n => 2*Real.sqrt (C*dimensionDecay (α-1) n+C*dimensionDecay (q-1) n))
      atTop (𝓝 0) := by
  have hh := ((dimensionDecay_tendsto (α-1) (by linarith)).const_mul C).add
    ((dimensionDecay_tendsto (q-1) (by linarith)).const_mul C)
  simpa using hh.sqrt.const_mul 2

lemma upper_polynomial_error_tendsto {C M θ m α δ q : ℝ}
    (hexp : 1+2*δ < α) (hα : 1 < α) (htail : 2 < θ*δ) (hq : 1 < q) :
    Tendsto (fun n => Real.sqrt (C/4*dimensionDecay (α-1) n +
      C/4*dimensionDecay (α-1-2*δ) n +
      2*C*M*Real.exp (θ*m)*dimensionDecay (θ*δ-2) n +
      C*dimensionDecay (q-1) n)) atTop (𝓝 0) := by
  have h1 := (dimensionDecay_tendsto (α-1) (by linarith)).const_mul (C/4)
  have h2 := (dimensionDecay_tendsto (α-1-2*δ) (by linarith)).const_mul (C/4)
  have h3 := (dimensionDecay_tendsto (θ*δ-2) (by linarith)).const_mul (2*C*M*Real.exp (θ*m))
  have h4 := (dimensionDecay_tendsto (q-1) (by linarith)).const_mul C
  simpa using ((h1.add h2).add h3 |>.add h4).sqrt

end SKGapCutoff

open MeasureTheory Filter
open scoped BigOperators Topology

end

end OAI
