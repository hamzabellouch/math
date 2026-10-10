import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFDerivativeConvergence
import OAI.Probability.SKBarriers.Gaussian.LipschitzCDFStability

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm s t ht x
  have HE := cdfDistance_subinterval_le (hnm n) hαm hs hst
  have HB := H.trans (mul_le_mul_of_nonneg_left HE (scalarTimeMassConstant_nonneg β))
  rw [Real.dist_eq,abs_sub_comm]
  exact HB.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) s t)
      (scalarCDFHessian β α s t) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFGradient_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFHessian_lipschitz β hα hαm s t ht)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFValue_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFGradient_lipschitz β hα hαm s t ht)
    (scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD s t ht hs hst)

theorem scalarCDFAverage_tendsto_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFAverage β (αn n) s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound
  rw [Real.dist_eq]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

end SK.Analytic

end
end

end OAI
