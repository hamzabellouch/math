import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.ClosureRegionInside

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

lemma region_boundary_hits_in_open {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V⊆U) (hconn : IsPreconnected U) (hne : (U\V).Nonempty)
    {π : V → D} (hπ : Continuous π) (d : D) (hd : (region V π d).Nonempty) :
    ∃ x∈U\V, d∈incident V π x := by
  by_contra hn
  have hbound : closure (region V π d)⊆region V π d∪Uᶜ := by
    intro x hx
    by_cases hxU : x∈U
    · left
      have hxV : x∈V := by by_contra hxV; exact hn ⟨x,⟨hxU,hxV⟩,hx⟩
      exact closure_region_inside hV hπ hx hxV
    · exact Or.inr hxU
  have hclosed : IsClosed (region V π d∪Uᶜ) := by
    apply isClosed_of_closure_subset
    rw [closure_union,hU.isClosed_compl.closure_eq]
    exact union_subset hbound subset_union_right
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set U := Subtype.val ⁻¹' region V π d
  have hC : IsClopen C := by
    constructor
    · have he : C=Subtype.val ⁻¹' (region V π d∪Uᶜ) := by
        ext x
        simp only [C,mem_preimage,mem_union,mem_compl_iff]
        exact or_iff_left (not_not.mpr x.property) |>.symm
      rw [he]
      exact hclosed.preimage continuous_subtype_val
    · exact (region_isOpen hV hπ d).preimage continuous_subtype_val
  obtain ⟨x,hx⟩ := hd
  have hxU : x∈U := hVU (region_subset _ _ _ hx)
  have hCe : C=univ := hC.eq_univ ⟨⟨x,hxU⟩,hx⟩
  obtain ⟨y,hyU,hyV⟩ := hne
  have hyC : (⟨y,hyU⟩ : U)∈C := hCe.symm ▸ mem_univ _
  exact hyV (region_subset _ _ _ hyC)
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
