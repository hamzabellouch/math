import Mathlib
import OAI.Probability.SKBarriers.Dynamics.HeatBathStationary
import OAI.Probability.SKBarriers.Dynamics.TVSignBridge

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def clockWeight (a : ℝ) (k : ℕ) : ℝ := Real.exp (-a)*a^k/(k.factorial:ℝ)

theorem clockWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ clockWeight a k := by
  unfold clockWeight
  positivity

theorem clockWeight_hasSum (a : ℝ) : HasSum (clockWeight a) 1 := by
  have H := (NormedSpace.expSeries_div_hasSum_exp a).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  unfold clockWeight
  simpa only [mul_div_assoc] using H

theorem clockWeight_sum (a : ℝ) : ∑' k : ℕ, clockWeight a k = 1 := (clockWeight_hasSum a).tsum_eq

theorem uniformization_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x y : Config n) :
    Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (clockWeight_nonneg (by positivity) k)
    (discreteKernel_nonneg β J k x y)) (fun k => ?_) (clockWeight_hasSum ((n:ℝ)*t)).summable
  exact mul_le_of_le_one_right (clockWeight_nonneg (by positivity) k) (discreteKernel_le_one hn β J k x y)

theorem continuousKernel_eq_clock {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : continuousKernel β J t x y =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y := by
  simp only [continuousKernel,clockWeight,neg_mul]

theorem continuousKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) {t : ℝ} (ht : 0 ≤ t)
    (x y : Config n) : 0 ≤ continuousKernel β J t x y := by
  rw [continuousKernel_eq_clock]
  apply tsum_nonneg
  intro k
  apply mul_nonneg
  · exact clockWeight_nonneg (by positivity) k
  · exact discreteKernel_nonneg β J k x y

theorem continuousKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x : Config n) : ∑ y : Config n, continuousKernel β J t x y = 1 := by
  classical
  simp_rw [continuousKernel_eq_clock]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) =>
    uniformization_summable hn β J ht x y)]
  simp_rw [← Finset.mul_sum,discreteKernel_sum hn,mul_one]
  exact clockWeight_sum _

theorem continuousKernel_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (y : Config n) :
    ∑ x : Config n, gibbs β J x*continuousKernel β J t x y = gibbs β J y := by
  classical
  simp_rw [continuousKernel_eq_clock]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun x (_ : x ∈ (Finset.univ : Finset (Config n))) =>
    (uniformization_summable hn β J ht x y).mul_left (gibbs β J x))]
  have HH (k : ℕ) : (∑ x : Config n, gibbs β J x*(clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y)) =
      clockWeight ((n:ℝ)*t) k*gibbs β J y := by
    simp_rw [mul_left_comm (gibbs β J _) (clockWeight ((n:ℝ)*t) k),← Finset.mul_sum,
      discreteKernel_stationary hn]
  simp_rw [HH]
  rw [tsum_mul_right,clockWeight_sum,one_mul]

theorem continuous_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) {t : ℝ} (ht : 0 ≤ t) (hTV : continuousDistance β J x t ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0 := by
  have H := finite_event_le_tv (continuousKernel β J t x) (gibbs β J)
    (continuousKernel_sum hn β J ht x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ continuousDistance β J x t at H
  linarith

end SK.Analytic

end
end

end

end OAI
