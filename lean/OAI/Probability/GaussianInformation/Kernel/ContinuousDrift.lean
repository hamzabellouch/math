import Mathlib
import OAI.Probability.GaussianInformation.Kernel.BayesContinuity

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma positive_continuous_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) (hc : ∀ w,Continuous (fun t => rule.prob t w)) :
    (∑ w,mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  let R := Scale.radius (DriftCutoff.level d H)
  have hR : 0 < R := Scale.radius_pos _
  let η : ℕ → ℝ := fun n => R/((n:ℝ)+1)
  have hη (n) : 0 < η n := div_pos hR (by positivity)
  have hηR (n) : η n ≤ R := div_le_self hR.le (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have ht : Tendsto η atTop (𝓝 0) := by
    have hh := tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := R)
    simpa only [mul_one_div,mul_zero] using hh
  have hconv (w : Fin N) : Tendsto (fun n => mass ν (rule.response (η n) w)*Phi (post ν (rule.response (η n) w))) atTop
      (𝓝 (mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w)))) := by
    apply tendsto_weighted_Phi_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
      (fun n => rule.response (η n) w) (rule.exactResponse w)
      (fun n => rule.measurable_response _ w) (rule.measurable_exactResponse w) rule.lower_pos
      (fun n s => (rule.response_bounds (hη n) w s).1)
      (fun s => (rule.exactResponse_bounds w s).1)
      (fun n s => (rule.response_bounds (hη n) w s).2)
      (fun s => (rule.exactResponse_bounds w s).2)
    exact ae_of_all _ (fun s => rule.tendsto_response hc w s η hη ht)
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconv w)) tendsto_const_nhds
    (fun n => positive_noisy_bound hd hN ν hH hν rule (hη n) (hηR n))

end KernelPotential.NoisyDrift

end OAI
