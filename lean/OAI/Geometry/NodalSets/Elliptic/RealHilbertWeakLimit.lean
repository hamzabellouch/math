import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

namespace OAI

namespace Yau
open Filter Set
open scoped Topology
noncomputable section

theorem real_hilbert_bounded_pairing_limit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (u : ℕ → E) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : E, ‖v‖ ≤ C ∧ ∀ (w : E) (a : ℝ),
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 a) → inner ℝ v w=a := by
  let f : ℕ → WeakDual ℝ E := fun n ↦ (InnerProductSpace.toDual ℝ E (u n)).toWeakDual
  have hmem : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro n
    simpa only [f,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨g,hg,hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) C).exists_mapClusterPt (f := atTop) (u := f)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem))
  let v := (InnerProductSpace.toDual ℝ E).symm g.toStrongDual
  refine ⟨v,?_,fun w a ha ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm g.toStrongDual‖ ≤ C
    simpa only [LinearIsometryEquiv.norm_map,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hg
  · have hc := hcluster.continuousAt_comp (WeakDual.eval_continuous w).continuousAt
    have hc' : MapClusterPt (inner ℝ v w) atTop (fun n ↦ inner ℝ (u n) w) := by
      simpa only [Function.comp_def,v,f,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply,
        StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply] using hc
    exact eq_of_nhds_neBot (hc'.clusterPt.mono ha).neBot

end
end Yau

end OAI
