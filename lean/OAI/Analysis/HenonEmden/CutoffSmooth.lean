import OAI.Analysis.HenonEmden.RadialIntegration

namespace OAI

universe uE

section CutoffSmooth

open MeasureTheory Set Filter Topology Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

lemma contDiff_etaProfile {n : ℕ} (hn : 1 ≤ n) : ContDiff ℝ 2 (etaProfile n) := by
  have hd : deriv (etaProfile n) = derivativeProfile n := funext (fun r => (hasDerivAt_etaProfile n r).deriv)
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,contDiff_succ_iff_deriv]
  refine ⟨fun r => (hasDerivAt_etaProfile n r).differentiableAt, by simp, ?_⟩
  rw [hd,contDiff_one_iff_deriv]
  refine ⟨fun r => (hasDerivAt_derivativeProfile hn r).differentiableAt, ?_⟩
  convert continuous_secondProfile n using 1
  exact funext (fun r => (hasDerivAt_derivativeProfile hn r).deriv)

lemma contDiff_eta {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (hn : 1 ≤ n) : ContDiff ℝ 2 (eta n : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with y hy
    exact eta_eq_one (mem_ball_zero_iff.mp hy).le
  · exact (contDiff_etaProfile hn).contDiffAt.comp _ (contDiffAt_norm ℝ hx)

end HenonLaneEmden.Cutoff
end
end CutoffSmooth

end OAI
