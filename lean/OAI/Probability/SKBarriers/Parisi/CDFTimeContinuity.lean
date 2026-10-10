import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTimeModulus

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_derivative_convergence_filter {ι : Type*} {l : Filter ι}
    {F D : ι → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ᶠ n in l, ∀ x, HasDerivAt (F n) (D n x) x)
    (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ᶠ n in l, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f l) : TendstoUniformly D d l := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ,hD,hLip] with n hn hdn hLn x
  have hb (z : ℝ) : |F n z-f z| ≤ δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hdn z).sub (hd z)) (hLn.sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

theorem scalarCDFValue_time_modulus_symmetric (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : s∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) (x : ℝ) :
    |scalarCDFValue β α s (Real.toNNReal (1-s)) x-
      scalarCDFValue β α q (Real.toNNReal (1-q)) x| ≤
      scalarTimeMassConstantK β 1*|s-q|+|β| *Real.sqrt |s-q| *standardGaussianAbsMoment := by
  rcases le_total s q with h | h
  · have H := scalarCDFValue_time_modulus β α ha h1 hs.1 h hq.2 x
    simpa only [abs_of_nonpos (sub_nonpos.mpr h),neg_sub] using H
  · have H := scalarCDFValue_time_modulus β α ha h1 hq.1 h hs.2 x
    rw [abs_sub_comm] at H
    simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using H

theorem scalarCDFValue_time_uniform (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    TendstoUniformly (fun s => scalarCDFValue β α s (Real.toNNReal (1-s)))
      (scalarCDFValue β α q (Real.toNNReal (1-q))) (𝓝[Icc (0:ℝ) 1] q) := by
  have hc : Continuous (fun s : ℝ => scalarTimeMassConstantK β 1*|s-q|+
      |β| *Real.sqrt |s-q| *standardGaussianAbsMoment) := by fun_prop
  have ht : Tendsto (fun s : ℝ => scalarTimeMassConstantK β 1*|s-q|+
      |β| *Real.sqrt |s-q| *standardGaussianAbsMoment) (𝓝[Icc (0:ℝ) 1] q) (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero,Real.sqrt_zero,zero_mul,zero_add] using
      (hc.continuousAt (x := q)).tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp ht).2 ε hε,self_mem_nhdsWithin] with s hs hsm x
  rw [Real.dist_eq,abs_sub_comm]
  exact (scalarCDFValue_time_modulus_symmetric β α ha h1 hsm hq x).trans_lt hs

theorem scalarCDFGradient_time_uniform (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    TendstoUniformly (fun s => scalarCDFGradient β α s (Real.toNNReal (1-s)))
      (scalarCDFGradient β α q (Real.toNNReal (1-q))) (𝓝[Icc (0:ℝ) 1] q) := by
  have hr {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : Real.toNNReal (1-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hs.1]
  apply uniform_derivative_convergence_filter 1 _
    (scalarCDFValue_hasDerivAt β ha α.mono q _ (hr hq)) _
    (scalarCDFGradient_lipschitz β ha α.mono q _ (hr hq))
    (scalarCDFValue_time_uniform β α ha h1 hq)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact scalarCDFValue_hasDerivAt β ha α.mono s _ (hr hs)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact scalarCDFGradient_lipschitz β ha α.mono s _ (hr hs)

theorem scalarCDFHessian_time_uniform (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    TendstoUniformly (fun s => scalarCDFHessian β α s (Real.toNNReal (1-s)))
      (scalarCDFHessian β α q (Real.toNNReal (1-q))) (𝓝[Icc (0:ℝ) 1] q) := by
  have hr {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : Real.toNNReal (1-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hs.1]
  apply uniform_derivative_convergence_filter susceptibilityLipschitzConstant _
    (scalarCDFGradient_hasDerivAt β ha α.mono q _ (hr hq)) _
    (scalarCDFHessian_lipschitz β ha α.mono q _ (hr hq))
    (scalarCDFGradient_time_uniform β α ha h1 hq)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact scalarCDFGradient_hasDerivAt β ha α.mono s _ (hr hs)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact scalarCDFHessian_lipschitz β ha α.mono s _ (hr hs)

end SK.Analytic

end
end

end OAI
