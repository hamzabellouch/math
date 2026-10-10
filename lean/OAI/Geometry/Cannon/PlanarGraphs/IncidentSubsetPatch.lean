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

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

omit [TopologicalSpace D] [DiscreteTopology D] in
lemma incident_subset_of_patch {V W : Set X} {π : V → D} (hW : IsOpen W)
    {d : D} (hl : W∩V⊆region V π d) {x : X} (hx : x∈W) :
    incident V π x⊆{d} := by
  intro e he
  obtain ⟨y,hyW,hyR⟩ := (mem_closure_iff_nhds.mp he) W (hW.mem_nhds hx)
  have hy := hl ⟨hyW,region_subset _ _ _ hyR⟩
  exact hyR.2.symm.trans hy.2
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
