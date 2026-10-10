import Mathlib
import OAI.Probability.GaussianInformation.Kernel.MassContinuity

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
namespace LocalRule
lemma positive_mass {k d N : ℕ} (rule : LocalRule k d N) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (w : Fin N) :
    mass ν ((rule.positive hN ε hε hε1).exactResponse w)=(1-ε)*mass ν (rule.response w)+ε/(N:ℝ) := by
  simp_rw [mass,rule.positive_response]
  rw [integral_add ((integrable_rule ν _ (rule.measurable_response w)
    (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2)).const_mul _) (integrable_const _),integral_const_mul]
  simp
lemma positive_post_zero {k d N : ℕ} (rule : LocalRule k d N) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w : Fin N) (ha : mass ν (rule.response w)=0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : post ν ((rule.positive hN ε hε hε1).exactResponse w)=ν := by
  have hr : rule.response w=ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg
    (fun s => (rule.response_bounds w s).1) (integrable_rule ν _ (rule.measurable_response w)
      (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2))).mp ha
  have hp : 0 < ε/(N:ℝ) := div_pos hε (by exact_mod_cast hN)
  rw [post,rule.positive_mass hN ν ε hε hε1 w,ha,mul_zero,zero_add]
  calc
    _ = ν.withDensity (fun _ => (1:ℝ≥0∞)) := withDensity_congr_ae (by
      filter_upwards [hr] with s hs
      rw [rule.positive_response,hs,Pi.zero_apply,mul_zero,zero_add,div_self hp.ne']
      simp)
    _ = ν := by simp
end LocalRule

lemma borel_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (rule : LocalRule (d/16) d N) :
    (∑ w,mass ν (rule.response w)*Phi (post ν (rule.response w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  let ε : ℕ → ℝ := fun n => (1/2:ℝ)/((n:ℝ)+1)
  have hε (n) : 0 < ε n := div_pos (by norm_num) (by positivity)
  have hε2 (n) : ε n ≤ (1/2:ℝ) := div_le_self (by norm_num) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hε1 (n) : ε n ≤ 1 := (hε2 n).trans (by norm_num)
  have ht : Tendsto ε atTop (𝓝 0) := by
    have hh := tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := (1/2:ℝ))
    simpa only [mul_one_div,mul_zero] using hh
  let R := fun n => rule.positive hN (ε n) (hε n) (hε1 n)
  have hconv (w : Fin N) : Tendsto (fun n => mass ν ((R n).exactResponse w)*Phi (post ν ((R n).exactResponse w))) atTop
      (𝓝 (mass ν (rule.response w)*Phi (post ν (rule.response w)))) := by
    have hg0 (s) := (rule.response_bounds w s).1
    have hg1 (s) := (rule.response_bounds w s).2
    have ha0 : 0 ≤ mass ν (rule.response w) := integral_nonneg hg0
    by_cases haz : mass ν (rule.response w)=0
    · have he (n) : post ν ((R n).exactResponse w)=ν := rule.positive_post_zero hN ν w haz (ε n) (hε n) (hε1 n)
      simp_rw [he,show ∀ n,mass ν ((R n).exactResponse w)=(1-ε n)*mass ν (rule.response w)+ε n/(N:ℝ) from
        fun _ => rule.positive_mass hN ν _ _ _ w,haz,mul_zero,zero_add,zero_mul]
      simpa using (ht.div_const (N:ℝ)).mul_const (Phi ν)
    · have hap : 0 < mass ν (rule.response w) := lt_of_le_of_ne ha0 (Ne.symm haz)
      apply tendsto_weighted_Phi_mass_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
        (fun n => (R n).exactResponse w) (rule.response w)
        (fun n => (R n).measurable_exactResponse w) (rule.measurable_response w)
        (fun n s => (R n).lower_pos.le.trans ((R n).exactResponse_bounds w s).1) hg0 (half_pos hap)
        (fun n => ?_) (by linarith)
        (fun n s => ((R n).exactResponse_bounds w s).2) hg1
      · apply ae_of_all
        intro s
        simp_rw [show ∀ n,(R n).exactResponse w s=(1-ε n)*rule.response w s+ε n/(N:ℝ) from
          fun _ => rule.positive_response hN _ _ _ w s]
        simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub ht).mul_const (rule.response w s)).add (ht.div_const (N:ℝ))
      · change _ ≤ mass ν ((rule.positive hN _ _ _).exactResponse w)
        rw [rule.positive_mass]
        have := hε2 n
        have hp : 0 ≤ ε n/(N:ℝ) := (div_pos (hε n) (by exact_mod_cast hN)).le
        nlinarith
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconv w)) tendsto_const_nhds
    (fun n => positive_borel_bound hd hN ν hH hν (R n))
end KernelPotential.NoisyDrift

end OAI
