import OAI.NumberTheory.Ostmann.Tree.ArrangementGraph
import OAI.NumberTheory.Ostmann.Tree.PartitionProducts

namespace OAI

/-! # Component products for the two arrangements of the same bulk variables -/

namespace Ostmann

open scoped BigOperators Classical

def bulkBlockProduct {L G : Type*} [CommMonoid G] {m : ℕ}
    (x : L × Fin m → G) (l : L) : G := ∏ j, x (l, j)

theorem component_block_product {L C G : Type*} [Fintype L] [CommMonoid G]
    (component : L → C) (m : ℕ) (x : L × Fin m → G) (c : C) :
    (∏ l : {l : L // component l = c}, bulkBlockProduct x l.1) =
      ∏ s : {s : L × Fin m // component s.1 = c}, x s.1 := by
  have h := (slotFiberEquiv component m c).prod_comp (fun lj => x (lj.1.1, lj.2))
  simpa only [slotFiberEquiv, Equiv.coe_fn_mk, Fintype.prod_prod_type,
    bulkBlockProduct] using h.symm

/-- Multiplying leaf products inside an actual overlap component gives
the same answer on both sides of the permutation. -/
theorem arrangement_partition_products {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (x : L × Fin m → G) :
    partitionProduct (arrangementLeft e) (bulkBlockProduct x) =
      partitionProduct (arrangementRight e) (bulkBlockProduct (x ∘ e.symm)) := by
  funext c
  change (∏ l : {l : L // arrangementLeft e l = c}, bulkBlockProduct x l.1) =
    ∏ l : {l : L // arrangementRight e l = c}, bulkBlockProduct (x ∘ e.symm) l.1
  rw [component_block_product, component_block_product]
  exact ((arrangementMatching e).restrict c).symm.prod_comp
    (fun s : {s : L × Fin m // arrangementLeft e s.1 = c} => x s.1) |>.symm

end Ostmann

end OAI
