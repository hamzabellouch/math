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

namespace CannonFaceLabels
open Set Topology CannonFaceIncidence

variable {X : Type*} [TopologicalSpace X]

theorem component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  have he : region V ConnectedComponents.mk (ConnectedComponents.mk x)=
      Subtype.val '' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨hy,hπ⟩
      exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hπ,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,ConnectedComponents.coe_eq_coe'.mpr hz⟩
  rw [he]
  exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
end CannonFaceLabels

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
