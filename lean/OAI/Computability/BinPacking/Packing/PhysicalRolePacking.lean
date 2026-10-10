import OAI.Computability.BinPacking.Inventory.InventoryPrefixConservation

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def packingOfRoleEquivs {Bin : Type*} [Fintype Bin]
    (e : ∀ r : Role, Bin ≃ D.RoleCopies r)
    (hcapacity : ∀ b, (∑ r : Role, D.itemSize ⟨r, e r b⟩) ≤ 1) :
    Packing D.packingInstance (Fintype.card Bin) := by
  classical
  let enum : Bin ≃ Fin (Fintype.card Bin) := Fintype.equivFin Bin
  let a : D.Item → Fin (Fintype.card Bin) := fun i => enum ((e i.1).symm i.2)
  refine packingOfFintype D.itemSize D.itemSize_pos D.itemSize_le_one a ?_
  intro j
  change (∑ i : (Σ r : Role, D.RoleCopies r),
    if enum ((e i.1).symm i.2) = j then D.itemSize i else 0) ≤ 1
  rw [Fintype.sum_sigma]
  have hsum : (∑ r : Role, ∑ c : D.RoleCopies r,
      if enum ((e r).symm c) = j then D.itemSize ⟨r, c⟩ else 0) =
      ∑ r : Role, D.itemSize ⟨r, e r (enum.symm j)⟩ := by
    apply Finset.sum_congr rfl
    intro r _
    rw [← (e r).sum_comp]
    have he (b : Bin) : enum b = j ↔ b = enum.symm j := by
      constructor
      · intro h
        exact enum.injective (h.trans (enum.apply_symm_apply j).symm)
      · rintro rfl
        exact enum.apply_symm_apply j
    simp only [Equiv.symm_apply_apply, he]
    simp
  rw [hsum]
  exact hcapacity (enum.symm j)

end BinPackingGap.InventoryData

end

end OAI
