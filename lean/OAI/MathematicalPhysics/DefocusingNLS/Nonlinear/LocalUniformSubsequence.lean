import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Subsequence extraction for locally equicontinuous complex functions -/

open Set Filter Topology

namespace DefocusingNLS

theorem exists_localUniform_subsequence {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (F : ℕ → C(X, ℂ)) (heq : Equicontinuous (fun n => (F n : X → ℂ)))
    (hb : ∀ x : X, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ v : C(X, ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (F ∘ φ) atTop (𝓝 v) := by
  let : T2Space (UniformOnFun X ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr (fun x =>
      mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have hemb : IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
      C(X, ℂ) → UniformOnFun X ℂ {K | IsCompact K}) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(X, ℂ) => (f : X → ℂ)) (fun K hK => hK) hemb
    · intro K _
      apply Equicontinuous.equicontinuousOn
      intro x U hU
      filter_upwards [heq x U hU] with y hy
      rintro ⟨f, n, rfl⟩
      exact hy n
    · intro K _ x _
      obtain ⟨M, hM⟩ := hb x
      refine ⟨Metric.closedBall (0 : ℂ) M, isCompact_closedBall _ _, ?_⟩
      rintro f ⟨n, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hM n
  obtain ⟨v, _, φ, hφ, hv⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨v, φ, hφ, hv⟩

end DefocusingNLS

end OAI
