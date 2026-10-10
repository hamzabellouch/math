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

namespace CannonFaceIncidence
open Set Topology

variable {X : Type*} [TopologicalSpace X]

lemma component_region_eq (V : Set X) (x : V) :
    region V ConnectedComponents.mk (ConnectedComponents.mk x)=connectedComponentIn V x.val := by
  rw [connectedComponentIn_eq_image x.property]
  ext y
  constructor
  · rintro ⟨hy,hye⟩
    exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hye,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,ConnectedComponents.coe_eq_coe'.mpr hy⟩

lemma component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  rw [component_region_eq]
  exact isConnected_connectedComponentIn_iff.mpr x.property

lemma component_regions_disjoint (V : Set X) {d e : ConnectedComponents V} (hne : d≠e) :
    Disjoint (region V ConnectedComponents.mk d) (region V ConnectedComponents.mk e) := by
  apply disjoint_left.mpr
  rintro x ⟨hx,hd⟩ ⟨hx',he⟩
  exact hne (hd.symm.trans he)
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

end OAI
