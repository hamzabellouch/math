import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFUniformQuantiles
import OAI.Probability.SKBarriers.Parisi.QuantileOverlapContinuity

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarOverlapModulus (β D h : ℝ) : ℝ :=
  (4*scalarTimeMassConstant β+2*scalarTimeMassConstantK β 3)*D/h+
    12*h+2*(Real.exp (2*(scalarTimeMassConstant β*D))-1)

theorem scalarOverlapModulus_tendsto (β h : ℝ) {D : ℕ → ℝ}
    (hD : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun n => scalarOverlapModulus β (D n) h) atTop (𝓝 (12*h)) := by
  have hc : Continuous (fun D : ℝ => scalarOverlapModulus β D h) := by
    unfold scalarOverlapModulus
    fun_prop
  simpa only [scalarOverlapModulus,mul_zero,zero_div,Real.exp_zero,sub_self,
    add_zero,zero_add,Function.comp_def] using hc.continuousAt.tendsto.comp hD

theorem scalarCDFOverlap_tendstoUniformlyOn (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => scalarCDFOverlap β (αn n))
      (scalarCDFOverlap β α) atTop (Icc (0:ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let h : ℝ := ε/48
  have hh : 0<h := div_pos hε (by norm_num)
  have he : 12*h<ε := by dsimp [h]; linarith
  have hev := (tendsto_order.mp (scalarOverlapModulus_tendsto β h hD)).2 ε he
  filter_upwards [hev] with n hnb x hx
  have H := scalarCDFOverlap_cdf_stability β (hn n) (hnm n) hα hαm hx h hh
  rw [Real.dist_eq,abs_sub_comm]
  exact H.trans_lt hnb

theorem scalarCDFOverlap_continuousOn (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) :
    ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1) := by
  have H := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono
    (fun k => quantileCDF_bounds k (uniformCDFQuantiles k α))
    (fun k => quantileCDF_monotone k (uniformCDFQuantiles k α))
    (uniformCDFQuantiles_L1_tendsto α ha h1)
  apply H.continuousOn
  exact Eventually.frequently (Eventually.of_forall (fun k =>
    scalarCDFOverlap_continuousOn_quantile β (uniformCDFQuantiles k α)
      (uniformCDFQuantiles_admissible k α h1)))

end SK.Analytic

end
end

end OAI
