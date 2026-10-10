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

namespace CannonFaceIncidence
variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

lemma closure_region_inside {V : Set X} (hV : IsOpen V) {π : V → D}
    (hπ : Continuous π) {d : D} {x : X} (hx : x∈closure (region V π d))
    (hxV : x∈V) : x∈region V π d := by
  let d₀ := π ⟨x,hxV⟩
  have hR := region_isOpen hV hπ d₀
  have hxR : x∈region V π d₀ := ⟨hxV,rfl⟩
  obtain ⟨y,⟨hyV,hyd₀⟩,⟨hyV',hyd⟩⟩ :=
    (mem_closure_iff_nhds.mp hx) _ (hR.mem_nhds hxR)
  exact ⟨hxV,hyd₀.symm.trans hyd⟩

theorem region_boundary_hits {K T : Set X} (hK : IsClosed K) (hT : IsClosed T)
    (hTK : T⊆K) (hconn : IsPreconnected Tᶜ) (hne : (K\T).Nonempty)
    {π : (Kᶜ : Set X) → D} (hπ : Continuous π) (d : D)
    (hd : (region Kᶜ π d).Nonempty) :
    ∃ x∈K, x∉T ∧ d∈incident Kᶜ π x := by
  by_contra hn
  have hbound : closure (region Kᶜ π d)⊆region Kᶜ π d∪T := by
    intro x hx
    by_cases hxK : x∈K
    · right
      by_contra hxT
      exact hn ⟨x,hxK,hxT,hx⟩
    · exact Or.inl (closure_region_inside hK.isOpen_compl hπ hx hxK)
  have hclosed : IsClosed (region Kᶜ π d∪T) := by
    apply isClosed_of_closure_subset
    rw [closure_union,hT.closure_eq]
    exact union_subset hbound subset_union_right
  let _ : PreconnectedSpace (Tᶜ : Set X) := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set (Tᶜ : Set X) := Subtype.val ⁻¹' region Kᶜ π d
  have hC : IsClopen C := by
    constructor
    · have he : C=Subtype.val ⁻¹' (region Kᶜ π d∪T) := by
        ext x
        simp only [C,mem_preimage,mem_union]
        exact or_iff_left x.property |>.symm
      rw [he]
      exact hclosed.preimage continuous_subtype_val
    · exact (region_isOpen hK.isOpen_compl hπ d).preimage continuous_subtype_val
  obtain ⟨x,hx⟩ := hd
  have hxT : x∉T := fun hxT => (region_subset Kᶜ π d hx) (hTK hxT)
  have hCe : C=univ := hC.eq_univ ⟨⟨x,hxT⟩,hx⟩
  obtain ⟨y,hyK,hyT⟩ := hne
  have hyC : (⟨y,hyT⟩ : (Tᶜ : Set X))∈C := hCe.symm ▸ mem_univ _
  exact (region_subset Kᶜ π d hyC) hyK
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

end OAI
