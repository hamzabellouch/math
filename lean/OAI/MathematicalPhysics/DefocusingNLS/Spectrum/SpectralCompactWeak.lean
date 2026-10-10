import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.Dual

namespace OAI

/-! Compact observations send bounded weakly null sequences to strongly null sequences. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralCompact_weakNull {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) (hT : IsCompactOperator T)
    (u : ℕ → E) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
  have hc := hT.isCompact_closure_image_closedBall M
  apply hc.tendsto_nhds_of_unique_mapClusterPt
  · exact Filter.Eventually.of_forall (fun n => subset_closure
      ⟨u n,by simpa only [Metric.mem_closedBall,dist_zero_right] using hu n,rfl⟩)
  · intro g _hg hcluster
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    intro L
    have he : MapClusterPt (L g) atTop (fun n => L (T (u n))) :=
      hcluster.continuousAt_comp L.continuous.continuousAt
    have hz := hweak (L.comp T)
    exact eq_of_nhds_neBot (he.clusterPt.mono hz)

end DefocusingNLS

end OAI
