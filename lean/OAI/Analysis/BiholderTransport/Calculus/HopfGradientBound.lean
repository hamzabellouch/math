import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.LocalMetricCharts
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_chart_hopf_gradient_bound (c:M) :
    ∃K≥0,∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c c),∀t:ℝ,1/2 ≤ t →
      ∀u:M → ℝ,Continuous u →
      ‖fderiv ℝ (fun w=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z‖ ≤ K := by
  let : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨L,r,hr,hT,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) c
  let D:ℝ≥0:=Real.toNNReal (Metric.diam (univ:Set M))
  have hD:∀x y:M,dist x y ≤ D := by
    intro x y
    rw [Real.coe_toNNReal _ Metric.diam_nonneg]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  refine ⟨2*(D:ℝ)*L,by positivity,?_⟩
  filter_upwards [ball_mem_nhds (extChartAt 𝓘(ℝ,Model n) c c) hr] with z hz
  intro t ht u hu
  have ht0:0 < t := by linarith
  have hn:=norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz)
    ((hopfLax_lipschitz hu hD ht0).comp_lipschitzOnWith hL)
  have hdiv:(D:ℝ)/t ≤ 2*D := (div_le_iff₀ ht0).mpr (by nlinarith [D.coe_nonneg])
  calc
    _ ≤ ↑((D/Real.toNNReal t)*L:ℝ≥0) := hn
    _ = (D:ℝ)/t*L := by rw [NNReal.coe_mul,NNReal.coe_div,Real.coe_toNNReal _ ht0.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiv L.coe_nonneg

end WeakMTWTransport

end

end OAI
