import Mathlib
import OAI.Probability.GaussianInformation.Kernel.JointEntropy

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity
lemma response_entropy_bound {d N : ℕ} (hN : 0 < N) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    -(∑ w,∫ s,xlog (rule.response η w s) ∂ν) ≤ Real.log (N:ℝ) := by
  have hi (w) : Integrable (fun s => xlog (rule.response η w s)) ν := integrable_xlog_bounded ν _
    (rule.measurable_response η w) (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2)
  rw [← integral_finsetSum _ (fun w _ => hi w),← integral_neg]
  have hh := integral_mono_ae (integrable_finsetSum _ (fun w _ => hi w)).neg (integrable_const (Real.log (N:ℝ))) (by
    filter_upwards [] with s
    have h := finite_entropy_bound hN (fun w => rule.response η w s)
      (fun w => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (rule.response_sum hη s)
    simpa only [xlog,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib] using h)
  simpa using hh

lemma cutoff_mass_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∑ w,mass ν (rule.response η w)*Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) ≤
      2*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+25*(d:ℝ) := by
  let a := fun w => mass ν (rule.response η w)
  have ha (w) : 0 < a w := rule.mass_pos hη ν w
  have ha1 (w) : a w ≤ 1 := rule.mass_le_one hη ν w
  have has : ∑ w,a w=1 := rule.mass_sum hη ν
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHd (w) : 1 ≤ H/a w := (le_div_iff₀ (ha w)).mpr (by simpa using (ha1 w).trans hH)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    mul_le_mul_of_nonneg_left (DriftCutoff.log_level_bound d (by omega) (hHd w)) (ha w).le)
  have he : (∑ w,a w*(2*Real.log (H/a w)/(d:ℝ)+25*(d:ℝ)))=
      (2/(d:ℝ))*(∑ w,a w*Real.log (H/a w))+25*(d:ℝ) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,has,one_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he,weighted_log_ratio a ha has hHp] at hh
  have hE := finite_entropy_bound hN a (fun w => (ha w).le) has
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2/(d:ℝ) by positivity)
  calc
    _ ≤ (2/(d:ℝ))*(Real.log H+∑ w,-a w*Real.log (a w))+25*(d:ℝ) := hh
    _ ≤ (2/(d:ℝ))*(Real.log H+Real.log (N:ℝ))+25*(d:ℝ) := by linarith
    _ = _ := by ring

lemma joint_postCharge_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
      ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) ≤
      35*(d:ℝ)+2*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  obtain ⟨M,_,hb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  rw [joint_integral_by_message ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_ne_top hη)
    (observationKernel_probability hη) rule.sum_kernel _ (measurable_postCharge hd ν hν rule hη)
    (fun z w => by rw [Real.norm_eq_abs,abs_of_nonneg (hb z w).1]; exact (hb z w).2)]
  simp only [PositiveRule.kernel,ENNReal.toReal_ofReal (rule.nonneg _ _)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => integrated_postCharge hd ν hH hν rule hη w)
  have hE := div_le_div_of_nonneg_right (response_entropy_bound hN ν rule hη) (show (0:ℝ) ≤ (d/16:ℕ) by positivity)
  have hL := cutoff_mass_bound hd hN ν hH rule hη
  simp_rw [mul_add] at hs
  simp only [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_neg_distrib,← Finset.sum_mul,rule.mass_sum hη ν,one_mul] at hs
  linarith

lemma positive_noisy_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η)
    (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have h1 := positive_noisy_comparison hd ν hH hν rule hη hηL
  have h2 := joint_postCharge_bound hd hN ν hH hν rule hη
  have h3 := DriftCutoff.log_level_bound d (by omega) hH
  linear_combination h1+h2+2*h3
end KernelPotential.NoisyDrift

end OAI
