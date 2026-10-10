import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Region

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonFaceIncidence
open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def homeomorphComponents (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  Equiv.ofBijective e.continuous.connectedComponentsMap
    (e.isQuotientMap.isCoinducing.connectedComponentsMap_bijective (fun y => by
      have he : e ⁻¹' {y}={e.symm y} := by
        ext x
        exact ⟨fun h => by simpa using congrArg e.symm h, fun h => by
          change x=e.symm y at h
          rw [h]
          exact e.apply_symm_apply y⟩
      rw [he]
      exact isConnected_singleton))

noncomputable def componentsDeletionEquiv (V : Set X) (S : Set X)
    [DiscreteTopology (ConnectedComponents V)] :
    ConnectedComponents (V\S : Set X) ≃
      Σ d : ConnectedComponents V, ConnectedComponents (region V ConnectedComponents.mk d\S : Set X) := by
  let U (d : ConnectedComponents V) : Set (V\S : Set X) :=
    {x | x.val∈region V ConnectedComponents.mk d}
  let π : (V\S : Set X) → ConnectedComponents V := fun x => ConnectedComponents.mk ⟨x.val,x.property.1⟩
  have hπ : Continuous π := ConnectedComponents.continuous_coe.comp (continuous_subtype_val.subtype_mk _)
  have hU (d : ConnectedComponents V) : U d=π ⁻¹' {d} := by
    ext x
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨x.property.1,h⟩
  have hcl (d : ConnectedComponents V) : IsClopen (U d) := by
    rw [hU]
    exact (isClopen_discrete {d}).preimage hπ
  have hdis : Pairwise (Function.onFun Disjoint U) := by
    intro d e hde
    apply Set.disjoint_left.mpr
    intro x hd he
    exact hde (hd.2.symm.trans he.2)
  have hcover : ⋃ d,U d=univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨π x,x.property.1,rfl⟩
  let E (d : ConnectedComponents V) : U d ≃ₜ (region V ConnectedComponents.mk d\S : Set X) :=
    { toFun := fun z => ⟨z.val.val,z.property,z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,(region_subset _ _ d z.property.1),z.property.2⟩,z.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (ConnectedComponents.equivOfIsClopen hcl hdis hcover).trans
    (Equiv.sigmaCongrRight fun d => homeomorphComponents (E d))

lemma region_disjoint_components (V : Set X) {d e : ConnectedComponents V} (hne : d≠e) :
    Disjoint (region V ConnectedComponents.mk d) (region V ConnectedComponents.mk e) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hne (hx.2.symm.trans hy.2)

lemma connected_components_card_one {U : Set X} (h : IsConnected U) :
    Nat.card (ConnectedComponents U)=1 := by
  let _ : ConnectedSpace U := isConnected_iff_connectedSpace.mp h
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
