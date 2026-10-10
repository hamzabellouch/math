import OAI.Combinatorics.SecondNeighborhood.SubsetAugmentation
import OAI.Combinatorics.SecondNeighborhood.Deletion

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deficitPotential_terminal (r : V → V → Prop) (S : Finset V) :
    deficitPotential r S (image r S \ S) =
      (image r (image r S) \ image r S).card := by
  classical
  have hsplit : (image r S ∩ S) ∪ (image r S \ S) = image r S := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_sdiff.mp hv).1
    · intro hv
      by_cases hs : v ∈ S
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hv, hs⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hv, hs⟩))
  unfold deficitPotential
  rw [hsplit]
  congr 1
  ext v
  constructor
  · intro hv
    obtain ⟨hpath, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := mem_image.mp hpath
    exact Finset.mem_sdiff.mpr
      ⟨mem_image.mpr ⟨u, (Finset.mem_sdiff.mp hu).1, huv⟩, hnot⟩
  · intro hv
    obtain ⟨hpath, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := mem_image.mp hpath
    have huS : u ∉ S := by
      intro huS
      exact hnot (mem_image.mpr ⟨u, huS, huv⟩)
    exact Finset.mem_sdiff.mpr
      ⟨mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huS⟩, huv⟩, hnot⟩

theorem subsetDeficit_of_minimal {r : V → V → Prop}
    (hr : IsOriented r) (hcounter : Counterexample r)
    (hminimal : ArcMinimal r) (hboundary : NonemptyBoundary r) :
    SubsetDeficit r := by
  classical
  intro S hS hproper
  have hE := hboundary S hS hproper
  have hg : deficitPotential r S (image r S \ S) < (image r S \ S).card := by
    apply strict_deficit_of_augmentation (image r S \ S) hE
      (deficitPotential r S)
    · simp [deficitPotential]
    · intro T hT hTproper
      exact deficitPotential_step r hr hcounter hminimal S T hT hTproper
  rw [deficitPotential_terminal] at hg
  exact hg

end SeymourSecondNeighborhood

end OAI
