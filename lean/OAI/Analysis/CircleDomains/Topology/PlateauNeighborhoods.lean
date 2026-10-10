import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates

namespace OAI

/-! Open sampling neighborhoods that preserve specified closed plateaus. -/

open Set
noncomputable section
namespace CircleDomainRigidity

def plateauNeighborhood (A V : Set EuclideanPlane) (x : EuclideanPlane) : Set EuclideanPlane := by
  classical
  exact if x ∈ A then V else Aᶜ

theorem isOpen_plateauNeighborhood {A V : Set EuclideanPlane}
    (hA : IsClosed A) (hV : IsOpen V) (x : EuclideanPlane) :
    IsOpen (plateauNeighborhood A V x) := by
  by_cases hx : x ∈ A
  · simpa only [plateauNeighborhood, ite_eq_left hx] using hV
  · simpa only [plateauNeighborhood, ite_eq_right hx] using hA.isOpen_compl

theorem self_mem_plateauNeighborhood {A V : Set EuclideanPlane}
    (hAV : A ⊆ V) (x : EuclideanPlane) : x ∈ plateauNeighborhood A V x := by
  by_cases hx : x ∈ A
  · simpa only [plateauNeighborhood, ite_eq_left hx] using hAV hx
  · simpa only [plateauNeighborhood, ite_eq_right hx, mem_compl_iff] using hx

theorem plateauNeighborhood_subset_of_meets {A V : Set EuclideanPlane} {x y : EuclideanPlane}
    (hy : y ∈ plateauNeighborhood A V x) (hyA : y ∈ A) :
    plateauNeighborhood A V x ⊆ V := by
  by_cases hx : x ∈ A
  · simp only [plateauNeighborhood, ite_eq_left hx, subset_refl]
  · have hn : y ∉ A := by simpa only [plateauNeighborhood, ite_eq_right hx, mem_compl_iff] using hy
    exact (hn hyA).elim

end CircleDomainRigidity

end

end OAI
