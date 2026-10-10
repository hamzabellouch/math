import OAI.Analysis.CircleDomains.Probability.ArcNullImage
import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import OAI.Analysis.CircleDomains.Uniformization.Conformal
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! Loop erasure for a continuous sphere path. Its compact image is a
locally connected quotient of the interval, so the published simple-arc
input is applied only to the connected open set `univ` in that image. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem locallyConnected_pathTime : LocallyConnectedSpace PathTime := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, ?_, hsub⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  have he : Subtype.val '' Metric.ball x r =
      Icc (0 : ℝ) 1 ∩ Metric.ball x.val r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hd⟩
      exact ⟨⟨y, hy⟩, hd, rfl⟩
  rw [he]
  exact (convex_Icc (0 : ℝ) 1 |>.inter (convex_ball x.val r)).isPreconnected

theorem exists_simple_subarc
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (γ : C(PathTime, Sphere)) (hne : γ ⊥ ≠ γ ⊤) :
    ∃ α : C(PathTime, Sphere), Injective α ∧ α ⊥ = γ ⊥ ∧ α ⊤ = γ ⊤ ∧
      range α ⊆ range γ := by
  let f : PathTime → range γ := fun t => ⟨γ t, mem_range_self t⟩
  have hf : Continuous f := γ.continuous.subtype_mk _
  have hsurj : Surjective f := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  let : LocallyConnectedSpace PathTime := locallyConnected_pathTime
  let : LocallyConnectedSpace (range γ) :=
    (Topology.IsQuotientMap.of_surjective_continuous hsurj hf).isCoinducing.locallyConnectedSpace
  have hc : IsCompact (range γ) := isCompact_range γ.continuous
  let : ConnectedSpace (range γ) := Subtype.connectedSpace (isConnected_range γ.continuous)
  have hconn : IsConnected (univ : Set (range γ)) :=
    isConnected_univ
  have hne' : f ⊥ ≠ f ⊤ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨a, ha, _⟩ := harcs (range γ) hc inferInstance univ isOpen_univ hconn
    (f ⊥) (by trivial) (f ⊤) (by trivial) hne'
  refine ⟨⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩,
    Subtype.val_injective.comp ha, congrArg Subtype.val a.source,
    congrArg Subtype.val a.target, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (a t).property

end CircleDomainRigidity

end

end OAI
