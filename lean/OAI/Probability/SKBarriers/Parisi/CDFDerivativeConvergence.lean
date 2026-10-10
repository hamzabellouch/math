import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_derivative_convergence {F D : ℕ → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x) (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ n, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f atTop) : TendstoUniformly D d atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ] with n hn x
  have hb (z : ℝ) : |F n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD n z).sub (hd z)) ((hLip n).sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

theorem scalarCDFValue_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) 0 1)
      (scalarCDFValue β α 0 1) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm 0 1 le_rfl x
  have HE : (∫ z in (0:ℝ)..0+(1:ℝ≥0), |αn n z-α z|)=cdfDistance (αn n) α := by
    simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc,cdfDistance]
  rw [HE] at H
  rw [Real.dist_eq,abs_sub_comm]
  exact H.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) 0 1)
      (scalarCDFHessian β α 0 1) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) 0 1 le_rfl x)
    (scalarCDFGradient_hasDerivAt β hα hαm 0 1 le_rfl)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) 0 1 le_rfl)
    (scalarCDFHessian_lipschitz β hα hαm 0 1 le_rfl)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) 0 1 le_rfl x)
    (scalarCDFValue_hasDerivAt β hα hαm 0 1 le_rfl)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) 0 1 le_rfl)
    (scalarCDFGradient_lipschitz β hα hαm 0 1 le_rfl)
    (scalarCDFValue_tendstoUniformly β hα hαm hn hnm hD)

end SK.Analytic

end
end

end OAI
