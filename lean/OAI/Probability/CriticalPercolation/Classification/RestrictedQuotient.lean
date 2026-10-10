import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.ComponentAction

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V Λ N T : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

lemma rangeRestrict_kernel_orbits (f : Λ →* N)
    (hf : ∀ v : V, (MulAction.orbit f.ker v).Finite) :
    ∀ v : V, (MulAction.orbit f.rangeRestrict.ker v).Finite := by
  intro v
  apply (hf v).subset
  rintro w ⟨g,hg⟩
  have hgm : f g.val=1 := congrArg Subtype.val g.property
  exact ⟨⟨g.val,hgm⟩,hg⟩

lemma rangeRestrict_stabilizer_images (f : Λ →* N)
    (hf : ∀ v : V, ((MulAction.stabilizer Λ v).map f : Set N).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map f.rangeRestrict : Set f.range).Finite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hf v)).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g,hg,rfl⟩

lemma component_quotient_le_kernel (ρ : Λ →* N) (φ : N →* T) (C : Set V) :
    (ρ.comp (componentKernel (φ.comp ρ) C).subtype).range≤φ.ker := by
  rintro n ⟨g,rfl⟩
  exact g.property.1

lemma infinite_index_of_le_coordinate_kernel [Infinite T]
    (φ : N →* T) (hφ : Surjective φ) (J : Subgroup N) (hJ : J≤φ.ker) :
    J.index=0 := by
  have hr : Infinite φ.range := Infinite.of_surjective φ.range.subtype
    (by intro t; obtain ⟨n,rfl⟩ := hφ t; exact ⟨⟨φ n,⟨n,rfl⟩⟩,rfl⟩)
  have hk : φ.ker.index=0 := by rw [Subgroup.index_ker,Nat.card_eq_zero_of_infinite]
  exact Nat.eq_zero_of_zero_dvd (hk ▸ Subgroup.index_dvd_of_le hJ)

end CriticalPercolation.BondGraph
end
end
end

end OAI
