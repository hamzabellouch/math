import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardJointBound

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma backward_gradient_sq_joint_bound {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    ∃ L : ℝ≥0, ∀ r ∈ Set.Icc (0:ℝ) b, ∀ s ∈ Set.Icc (0:ℝ) b, ∀ z y,
      |(deriv (backward c b f r) z)^2-(deriv (backward c b f s) y)^2| ≤
        (L:ℝ)*(|r-s|+|z-y|) := by
  obtain ⟨L,hL⟩ := backward_gradient_joint_bound hf hLip hc b
  refine ⟨2*L,fun r hr s hs z y => ?_⟩
  have hu := (backward_verificationData hf hLip hc b).gradient_bound r z
  have hv := (backward_verificationData hf hLip hc b).gradient_bound s y
  have hdiff := hL r hr s hs z y
  rw [sq_sub_sq,abs_mul]
  have hsum : |deriv (backward c b f r) z+deriv (backward c b f s) y| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hprod := mul_le_mul hdiff hsum (abs_nonneg _) (by positivity : 0 ≤ (L:ℝ)*(|r-s|+|z-y|))
  simp only [NNReal.coe_mul,NNReal.coe_ofNat]
  nlinarith [hprod]

lemma continuousOn_backward_source_heat {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    ContinuousOn (fun r => varianceHeat (r-a) (fun z => (deriv (backward c b f r) z)^2) x)
      (Set.Icc a b) := by
  obtain ⟨L,hL⟩ := backward_gradient_sq_joint_bound hf hLip hc b
  exact continuousOn_moving_heat hab
    (fun r => ((regularDatum_varianceLogHeat hf hLip hc (b-r)).deriv_bounded.smooth.continuous.measurable.pow_const 2))
    (fun r hr s hs => hL r ⟨ha.trans hr.1,hr.2⟩ s ⟨ha.trans hs.1,hs.2⟩) x

lemma backward_mild {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    backward c b f a x = varianceHeat (b-a) f x+
      (c/2)*(∫ r in a..b, varianceHeat (r-a) (fun z => (deriv (backward c b f r) z)^2) x) := by
  obtain ⟨L,hL⟩ := backward_joint_bound hf hLip hc b
  have hcont := continuousOn_moving_heat hab
    (fun r => (regularDatum_varianceLogHeat hf hLip hc (b-r)).smooth.continuous.measurable)
    (fun r hr s hs => hL r ⟨ha.trans hr.1,hr.2⟩ s ⟨ha.trans hs.1,hs.2⟩) x
  have hint : IntervalIntegrable (fun r => -(c/2)*varianceHeat (r-a) (fun z => (deriv (backward c b f r) z)^2) x) volume a b :=
    ((continuousOn_backward_source_heat hf hLip hc ha hab x).const_mul (-(c/2))).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun r hr => hasDerivAt_moving_backward_heat hf hLip hc hr.1 hr.2 x) hint
  have ht : varianceLogHeat c 0 f = f := by
    funext z
    simpa only [backward,sub_self] using backward_terminal c b f z
  simp only [intervalIntegral.integral_const_mul,sub_self,ht,varianceHeat_zero] at he
  change varianceLogHeat c (b-a) f x = _
  linarith

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
