import Mathlib

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPaths
abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

lemma sphere_locallyPathConnected : LocallyPathConnectedSpace SphereTwo := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  exact ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) SphereTwo

lemma sphere_punctured_pathConnected (p : SphereTwo) :
    IsPathConnected ({p}ᶜ : Set SphereTwo) := by
  have hc := (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere p)).continuous
  have hh := isPathConnected_range hc
  have he : Set.range (stereographic (norm_eq_of_mem_sphere p)).symm = {p}ᶜ :=
    range_stereographic_symm (norm_eq_of_mem_sphere p) p.property
  rw [← he]
  exact hh

lemma sphere_pathConnected : PathConnectedSpace SphereTwo := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  simp

end CannonPaths

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
