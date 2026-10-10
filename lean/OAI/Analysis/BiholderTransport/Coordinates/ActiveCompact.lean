import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isCompact_total_activeLogs {v : M → ℝ} (hv : Continuous v) :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs (n := n) v z.1} := by
  cases isEmpty_or_nonempty M with
  | inl h =>
      have he : {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs (n := n) v z.1}=∅ := by
        ext z
        exact isEmptyElim z.1
      rw [he]
      exact isCompact_empty
  | inr h =>
      have hc : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
          contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2)) := by
        have hp : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
          FiberBundle.continuous_proj _ _
        have he := (contMDiff_riemannianExp (n := n) (M := M)).continuous
        exact (((continuous_cTransform hv).comp hp).add
          (((hp.dist he).pow 2).div_const 2)).add (hv.comp he)
      exact (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
        (isClosed_eq hc continuous_const)

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_hull_norm_le_diam {v : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    ‖p‖≤Metric.diam (univ : Set M) := by
  have hs : activeLogs (n := n) v x ⊆
      Metric.closedBall (0 : TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M)) := by
    intro q hq
    rw [Metric.mem_closedBall,dist_zero_right,←hq.1]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (convexHull_min hs (convex_closedBall _ _)) hp

lemma exists_uniform_short_contraction_into_ID (D : ℝ) :
    ∃ τ>0, τ<1 ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤D → ∀ t : ℝ, 0≤t → t≤τ → t • p ∈ injectivityDomain x := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  have hK := isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) D
  have H : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      ‖z.2‖≤D → t • z.2 ∈ injectivityDomain z.1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have ho := (isOpen_total_injectivityDomain (n := n) (M := M)).preimage
      (contMDiff_tangentScale (E := Model n) (M := M)).continuous
    apply ho.mem_nhds
    change (0:ℝ) • z.2 ∈ injectivityDomain z.1
    simpa only [zero_smul] using zero_mem_injectivityDomain (n := n) z.1
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  obtain ⟨τ,hτ,hτm⟩ := exists_between (lt_min hδ (show (0:ℝ)<1 by norm_num))
  refine ⟨τ,hτ,(lt_min_iff.mp hτm).2,?_⟩
  intro x p hp t ht htτ
  exact Hδ (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht] using
    htτ.trans_lt (lt_min_iff.mp hτm).1) ⟨x,p⟩ hp

lemma exists_uniform_short_active_hull_contraction :
    ∃ τ>0, τ<1 ∧ ∀ v : M → ℝ, ∀ x : M,
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
        ∀ t : ℝ, 0≤t → t≤τ → t • p ∈ injectivityDomain x := by
  obtain ⟨τ,hτ,hτ1,H⟩ := exists_uniform_short_contraction_into_ID (n := n) (M := M)
    (Metric.diam (univ : Set M))
  exact ⟨τ,hτ,hτ1,fun _ x p hp => H x p (active_hull_norm_le_diam hp)⟩

end WeakMTWTransport

end

end OAI
