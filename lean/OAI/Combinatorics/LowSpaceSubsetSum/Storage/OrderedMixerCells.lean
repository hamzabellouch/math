import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredOrderedMixers

namespace OAI

/-! # Retained arrays for the three computed mixer domains -/

namespace LowSpaceSubsetSum.OrderedMixerCells

open scoped BigOperators
variable {n : ℕ}

def run (data : RepresentationLayoutPreparation.Data n) :
    (Option (StoredOrderedMixers.Domains n) × ℕ) × ℕ :=
  let xs := StoredOrderedMixers.lists data
  if h : ∀ j : Fin 3, xs[j.val].length = PartitionLabelExecution.size n j then
    ((some (fun j => StoredPartitionBlocks.domain xs[j.val] (h j)),
      2*(∑ j : Fin 3, xs[j.val].length)+10),
      8*(∑ j : Fin 3, xs[j.val].length)+64)
  else ((none, 2*(∑ j : Fin 3, xs[j.val].length)+10),
    4*(∑ j : Fin 3, xs[j.val].length)+64)

theorem value (data : RepresentationLayoutPreparation.Data n) :
    (run data).1 = StoredOrderedMixers.run data := by
  simp only [run, StoredOrderedMixers.run]
  split <;> simp_all only

theorem cells (data : RepresentationLayoutPreparation.Data n)
    (hl : ∀ j : Fin 3, data.domains[j.val].length ≤ n) :
    (run data).2 ≤ 24*n+64 := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    hl data.parameters.order[j.val])
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  unfold run
  dsimp only
  split <;> simp only [StoredOrderedMixers.lists, Vector.getElem_ofFn] <;> omega

end LowSpaceSubsetSum.OrderedMixerCells

end OAI
