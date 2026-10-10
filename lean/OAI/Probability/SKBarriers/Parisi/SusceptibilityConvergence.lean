import Mathlib
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Gaussian.LipschitzTerminalStability
import OAI.Probability.SKBarriers.Parisi.CDFIntervalConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilityAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilityAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := scalarCDFHessian β α r s
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n => scalarCDFHessian β (αn n) r s
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

end SK.Analytic

end
end

end OAI
