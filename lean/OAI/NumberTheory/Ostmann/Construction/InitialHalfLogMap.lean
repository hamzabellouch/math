import OAI.NumberTheory.Ostmann.Construction.InitialHalfLogSlots

namespace OAI

/-! # Reindexing the original half-cutoff lists without changing their weights -/
namespace Ostmann
open scoped Classical

theorem initialHalfBulkLeaves_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (side : Bool) :
    initialHalfBulkLeaves n b (g ∘ slot) side =
      treeLeafMap (List.map g) n (initialHalfBulkLeaves n b slot side) := by
  unfold initialHalfBulkLeaves
  rw [bulkSlotLeaves_map]
  rfl

theorem initialHalfLogSlots_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (j : Fin (2 ^ n + 2 ^ n)) :
    initialHalfLogSlots n b (g ∘ slot) j = (initialHalfLogSlots n b slot j).map g := by
  unfold initialHalfLogSlots
  have he : initialHalfBulkLeaves n b (g ∘ slot) =
      fun side => treeLeafMap (List.map g) n (initialHalfBulkLeaves n b slot side) := by
    funext side
    exact initialHalfBulkLeaves_map g n b slot side
  rw [he]
  exact movingBulkPairedCutoffSlots_map n (initialHalfBulkLeaves n b slot) g j

theorem initialPairedHalfLogSlots_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B)
    (j : Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n))) :
    initialPairedHalfLogSlots n b (fun side => g ∘ slot side) j =
      (initialPairedHalfLogSlots n b slot j).map g := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simpa only [initialPairedHalfLogSlots, Fin.append_left] using
      initialHalfLogSlots_map g n b (slot false) i
  · simpa only [initialPairedHalfLogSlots, Fin.append_right] using
      initialHalfLogSlots_map g n b (slot true) i

end Ostmann

end OAI
