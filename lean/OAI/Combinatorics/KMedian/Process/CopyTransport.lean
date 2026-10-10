import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyState

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

noncomputable def localSet (A S : Finset (Copy (F := F) Δ)) : Finset A :=
  univ.filter (fun i => i.val ∈ S)

@[simp] theorem mem_localSet (A S : Finset (Copy (F := F) Δ)) (i : A) :
    i ∈ localSet A S ↔ i.val ∈ S := by simp [localSet]

 theorem localSet_image (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) :
    (localSet A S).image Subtype.val=S := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact (mem_localSet _ _ _).mp hj
  · intro hi
    exact mem_image.mpr ⟨⟨i,hS hi⟩,(mem_localSet _ _ _).mpr hi,rfl⟩

 theorem image_mass (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ) :
    mass g (S.image Subtype.val)=mass g S := by
  simp only [mass,card_image_of_injective _ Subtype.val_injective]

 theorem image_cost (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g d (S.image Subtype.val)=
      PhysicalPotential.cost g (fun i => d i.val) S := by
  unfold PhysicalPotential.cost
  rw [sum_image (fun _ _ _ _ he => Subtype.ext he)]

 theorem localSet_mass (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ) :
    mass g (localSet A S)=mass g S := by
  rw [← image_mass,localSet_image A S hS]

 theorem localSet_cost (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    PhysicalPotential.cost g (fun i => d i.val) (localSet A S)=PhysicalPotential.cost g d S := by
  rw [← image_cost,localSet_image A S hS]

 theorem image_potential (A : Finset (Copy (F := F) Δ)) (S : Finset A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g d (S.image Subtype.val) b=potential x g (fun i => d i.val) S b := by
  unfold potential
  rw [image_mass,image_cost]

 theorem localSet_potential (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (x g b : ℝ)
    (d : Copy (F := F) Δ → ℝ) :
    potential x g (fun i => d i.val) (localSet A S) b=potential x g d S b := by
  rw [← image_potential,localSet_image A S hS]

 theorem localSet_sdiff (A S T : Finset (Copy (F := F) Δ)) :
    localSet A (S \ T)=localSet A S \ localSet A T := by
  ext i
  simp

end MetricKMedian.CopyState
end
end

end OAI
