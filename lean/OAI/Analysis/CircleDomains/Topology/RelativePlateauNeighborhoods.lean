import OAI.Analysis.CircleDomains.Sobolev.PartitionPlateaus

namespace OAI

/-! Plateau refinement for relatively closed sets in the physical domain,
including terminal collars that reach deleted boundary components. -/

open Set
noncomputable section
namespace CircleDomainRigidity

def relativePlateauNeighborhood (D A V : Set EuclideanPlane)
    (x : EuclideanPlane) : Set EuclideanPlane := by
  classical
  exact if x ∈ A then V else D \ A

theorem isOpen_relativePlateauNeighborhood {D A V : Set EuclideanPlane}
    (hA : IsOpen (D \ A)) (hV : IsOpen V) (x : EuclideanPlane) :
    IsOpen (relativePlateauNeighborhood D A V x) := by
  by_cases hx : x ∈ A
  · simpa only [relativePlateauNeighborhood, ite_eq_left hx] using hV
  · simpa only [relativePlateauNeighborhood, ite_eq_right hx] using hA

theorem self_mem_relativePlateauNeighborhood {D A V : Set EuclideanPlane}
    (hAV : A ⊆ V) {x : EuclideanPlane} (hxD : x ∈ D) :
    x ∈ relativePlateauNeighborhood D A V x := by
  by_cases hx : x ∈ A
  · simpa only [relativePlateauNeighborhood, ite_eq_left hx] using hAV hx
  · simpa only [relativePlateauNeighborhood, ite_eq_right hx] using (show x ∈ D \ A from ⟨hxD, hx⟩)

theorem relativePlateauNeighborhood_subset_of_meets
    {D A V : Set EuclideanPlane} {x y : EuclideanPlane}
    (hy : y ∈ relativePlateauNeighborhood D A V x) (hyA : y ∈ A) :
    relativePlateauNeighborhood D A V x ⊆ V := by
  by_cases hx : x ∈ A
  · simp only [relativePlateauNeighborhood, ite_eq_left hx, subset_refl]
  · have hn : y ∈ D \ A := by
      simpa only [relativePlateauNeighborhood, ite_eq_right hx] using hy
    exact (hn.2 hyA).elim

theorem partition_samples_within_relative_plateau
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (center : ι → EuclideanPlane) (A V : Set EuclideanPlane)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (hW : ∀j, W j ⊆ relativePlateauNeighborhood Ω A V (center j)) :
    ∀x ∈ A, ∀j, ρ.weight j x ≠ 0 → W j ⊆ V := by
  intro x hx j hj
  have hxW := hsub j (subset_tsupport (ρ.weight j) hj)
  exact (hW j).trans (relativePlateauNeighborhood_subset_of_meets (hW j hxW) hx)

end CircleDomainRigidity

end

end OAI
