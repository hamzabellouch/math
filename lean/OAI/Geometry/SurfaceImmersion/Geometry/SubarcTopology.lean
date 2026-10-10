import OAI.Geometry.SurfaceImmersion.Geometry.EmbeddedOpenSubset
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Open subarcs are connected, and their only possible frontier points
are their two endpoints. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem CompactCurveArc.subarc_frontier (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v)
    {x : X} (hx : x ∈ closure (A.openSubarc u v)) (hnot : x ∉ A.openSubarc u v) :
    x = A.map ⟨u,hu,huv.le.trans hv⟩ ∨ x = A.map ⟨v,hu.trans huv.le,hv⟩ := by
  have hsub : A.openSubarc u v ⊆ A.closedSubarc u v := by
    rintro z ⟨t,ht,rfl⟩
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hc := closure_minimal hsub (A.closedSubarc_compact u v).isClosed
  obtain ⟨t,ht,rfl⟩ := hc hx
  have hnt : ¬ (u < (t:ℝ) ∧ (t:ℝ) < v) := fun h => hnot ⟨t,h,rfl⟩
  rcases eq_or_lt_of_le ht.1 with he | he
  · left
    congr 1
    exact Subtype.ext he.symm
  · right
    have heq : (t:ℝ) = v := le_antisymm ht.2 (le_of_not_gt fun h => hnt ⟨he,h⟩)
    congr 1
    exact Subtype.ext heq

omit [T2Space X] in
theorem CompactCurveArc.subarc_connected (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v) :
    IsConnected (A.openSubarc u v) := by
  let j : Ioo u v → Icc A.left A.right := fun t =>
    ⟨t.val,hu.trans t.property.1.le,t.property.2.le.trans hv⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let : ConnectedSpace (Ioo u v) := isConnected_iff_connectedSpace.mp (isConnected_Ioo huv)
  have hconn : IsConnected (range (A.map ∘ j)) := isConnected_range (A.embedding.continuous.comp hj)
  have heq : range (A.map ∘ j) = A.openSubarc u v := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨j t,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,ht⟩,rfl⟩
  rwa [heq] at hconn

theorem CompactCurveArc.subarc_clopen_complement (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v)
    (V : Set X)
    (hleft : A.map ⟨u,hu,huv.le.trans hv⟩ ∈ V)
    (hright : A.map ⟨v,hu.trans huv.le,hv⟩ ∈ V) :
    IsClopen ((↑) ⁻¹' A.openSubarc u v : Set {x : X // x ∉ V}) := by
  have heq : ((↑) ⁻¹' A.openSubarc u v : Set {x : X // x ∉ V}) = (↑) ⁻¹' closure (A.openSubarc u v) := by
    ext x
    constructor
    · exact fun hx => subset_closure hx
    · intro hx
      by_contra hn
      rcases A.subarc_frontier hu hv huv hx hn with he | he
      · exact x.property (he ▸ hleft)
      · exact x.property (he ▸ hright)
  refine ⟨?_,(A.openSubarc_open hu hv).preimage continuous_subtype_val⟩
  rw [heq]
  exact isClosed_closure.preimage continuous_subtype_val

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
