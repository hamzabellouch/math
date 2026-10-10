import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLayoutPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPartitionBlocks

namespace OAI

/-! # Reading the computed mixer order into three stored domains

The only order read by this program is the three-entry integer parameter
array. A length guard makes the subsequent label-array reads total.
-/

namespace LowSpaceSubsetSum.StoredOrderedMixers

open scoped BigOperators
variable {n : ℕ}

def lists (data : RepresentationLayoutPreparation.Data n) : Vector (List (Fin n)) 3 :=
  Vector.ofFn (fun j : Fin 3 => data.domains[data.parameters.order[j.val].val])

abbrev Domains (n : ℕ) := ∀ j : Fin 3, Vector (Fin n) (PartitionLabelExecution.size n j)

def run (data : RepresentationLayoutPreparation.Data n) : Option (Domains n) × ℕ :=
  let xs := lists data
  if h : ∀ j : Fin 3, xs[j.val].length = PartitionLabelExecution.size n j then
    (some (fun j => StoredPartitionBlocks.domain xs[j.val] (h j)),
      2 * (∑ j : Fin 3, xs[j.val].length) + 10)
  else (none, 2 * (∑ j : Fin 3, xs[j.val].length) + 10)

theorem run_of_lengths (data : RepresentationLayoutPreparation.Data n)
    (h : ∀ j : Fin 3, (lists data)[j.val].length = PartitionLabelExecution.size n j) :
    (run data).1 = some (fun j => StoredPartitionBlocks.domain (lists data)[j.val] (h j)) := by
  unfold run
  dsimp only
  rw [dite_eq_left h]

theorem lists_source (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed)
    (data : RepresentationLayoutPreparation.Data n) (h : (RepresentationLayoutPreparation.run D s).1 = some data)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, data.permutation[i.val] = e i)
    (signs : Finset (Fin n)) (j : Fin 3) :
    (lists data)[j.val] = (D.zeroSetup.orderedMixers (e, signs) j).sort (· ≤ ·) := by
  have hp := RepresentationLayoutPreparation.prepared D s data h
  have hd := congrArg Prod.fst hp
  have ho := congrArg Prod.snd hp
  dsimp only at hd ho
  simp only [lists, Vector.getElem_ofFn]
  simp only [ho, RepresentationParameterPreparation.order_value D data.permutation e hv signs, hd]
  exact RepresentationMixerPreparation.domains_value D data.permutation e hv _

theorem complete (D : RepresentationData n) (s : D.zeroSetup.layoutCoupling.Seed)
    (data : RepresentationLayoutPreparation.Data n) (h : (RepresentationLayoutPreparation.run D s).1 = some data)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, data.permutation[i.val] = e i)
    (signs : Finset (Fin n)) :
    ∃ domains, (run data).1 = some domains ∧
      ∀ (j : Fin 3) (k : Fin (PartitionLabelExecution.size n j)),
        (domains j)[k.val] = ((CanonicalPartition.ranks D.zeroSetup (e, signs) j).symm k).val := by
  have hx := lists_source D s data h e hv signs
  have hl (j : Fin 3) : (lists data)[j.val].length = PartitionLabelExecution.size n j := by
    rw [hx j, Finset.length_sort]
    exact CanonicalPartition.size_eq D.zeroSetup (e, signs) j
  refine ⟨fun j => StoredPartitionBlocks.domain (lists data)[j.val] (hl j),
    run_of_lengths data hl, ?_⟩
  intro j k
  exact StoredPartitionBlocks.domain_source D.zeroSetup (e, signs) j _ (hl j) (hx j) k

theorem work (data : RepresentationLayoutPreparation.Data n)
    (hl : ∀ j : Fin 3, data.domains[j.val].length ≤ n) :
    (run data).2 ≤ 6 * n + 10 := by
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    hl data.parameters.order[j.val])
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  unfold run
  dsimp only
  split <;> simp only [lists, Vector.getElem_ofFn] <;> omega

end LowSpaceSubsetSum.StoredOrderedMixers

end OAI
