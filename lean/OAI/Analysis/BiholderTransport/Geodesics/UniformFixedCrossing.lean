import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.UniformRegularSplit

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
  (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizing_norm_le_diam {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : ‖p‖ ≤ Metric.diam (univ : Set M) := by
  rw [←hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

lemma exists_actual_uniform_regular_split :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
        h • p∈injectivityDomain x ∧
        (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
          injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  obtain ⟨h,hh,hh1,Hh⟩ := exists_uniform_regular_split (n := n) (M := M) (Metric.diam (univ : Set M))
  exact ⟨h,hh,hh1,fun x p hp => Hh x p (minimizing_norm_le_diam hp) hp⟩

end WeakMTWTransport

end

end OAI
