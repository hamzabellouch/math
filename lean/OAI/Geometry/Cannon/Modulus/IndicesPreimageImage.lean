import Mathlib
import OAI.Geometry.Cannon.Modulus.Weights

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCells

open CannonDuality

variable {X Y ι : Type*} [Fintype ι]

lemma indices_preimage_image (e : X → Y) (C : ι → Set Y) (A : Set X) :
    indices (fun i => e ⁻¹' C i) A = indices C (e '' A) := by
  ext i
  rw [mem_indices,mem_indices]
  constructor
  · rintro ⟨x,hx,hc⟩
    exact ⟨e x,⟨x,hx,rfl⟩,hc⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,hc⟩
    exact ⟨x,hx,hc⟩

lemma incidence_preimage_image (e : X → Y) (C : ι → Set Y) (A : Set X) :
    incidence (fun i => e ⁻¹' C i) A = incidence C (e '' A) := by
  unfold incidence
  rw [indices_preimage_image]

lemma familyVectors_preimage_image (e : X → Y) (C : ι → Set Y) (F : Set (Set X)) :
    familyVectors (fun i => e ⁻¹' C i) F =
      familyVectors C {B | ∃ A ∈ F, B = e '' A} := by
  ext v
  rw [mem_familyVectors,mem_familyVectors]
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨e '' A,⟨A,hA,rfl⟩,(incidence_preimage_image e C A).symm⟩
  · rintro ⟨B,⟨A,hA,rfl⟩,rfl⟩
    exact ⟨A,hA,incidence_preimage_image e C A⟩

lemma modulus_preimage_image (e : X → Y) (C : ι → Set Y) (F : Set (Set X)) :
    modulus (fun i => e ⁻¹' C i) F = modulus C {B | ∃ A ∈ F, B = e '' A} := by
  unfold modulus
  rw [familyVectors_preimage_image]

end CannonCells

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
