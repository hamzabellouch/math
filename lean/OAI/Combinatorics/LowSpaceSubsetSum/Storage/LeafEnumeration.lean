import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResourceMoments
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDictionary

namespace OAI

/-! # Executable indexed raw-leaf enumeration -/

namespace LowSpaceSubsetSum

variable {n : ℕ}

/-- Each indexed subset is generated in the fixed input-index order. -/
def subsetList (V : Finset (Fin n)) : List (Finset (Fin n)) :=
  (V.sort (· ≤ ·)).sublists.map List.toFinset

/-- Fixed-size selections use the corresponding finite sublist generator. -/
def fixedSubsetList (V : Finset (Fin n)) (k : ℕ) : List (Finset (Fin n)) :=
  ((V.sort (· ≤ ·)).sublistsLen k).map List.toFinset

theorem subsetList_mem (V S : Finset (Fin n)) : S ∈ subsetList V ↔ S ⊆ V := by
  constructor
  · intro h
    obtain ⟨indices, hi, rfl⟩ := List.mem_map.mp h
    intro i hm
    exact (Finset.mem_sort (· ≤ ·)).mp
      ((List.mem_sublists.mp hi).subset (List.mem_toFinset.mp hm))
  · intro hS
    let indices := (V.sort (· ≤ ·)).filter (fun i => i ∈ S)
    have he : indices.toFinset = S := by
      ext i
      simp only [indices, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
      exact ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
    exact List.mem_map.mpr ⟨indices, List.mem_sublists.mpr List.filter_sublist, he⟩

theorem fixedSubsetList_mem (V S : Finset (Fin n)) (k : ℕ) :
    S ∈ fixedSubsetList V k ↔ S ⊆ V ∧ S.card = k := by
  constructor
  · intro h
    obtain ⟨indices, hi, rfl⟩ := List.mem_map.mp h
    obtain ⟨hi, hlen⟩ := List.mem_sublistsLen.mp hi
    refine ⟨?_, ?_⟩
    · intro i hm
      exact (Finset.mem_sort (· ≤ ·)).mp (hi.subset (List.mem_toFinset.mp hm))
    · rw [List.toFinset_card_of_nodup (hi.nodup (Finset.sort_nodup _ _)), hlen]
  · rintro ⟨hS, hcard⟩
    let indices := (V.sort (· ≤ ·)).filter (fun i => i ∈ S)
    have he : indices.toFinset = S := by
      ext i
      simp only [indices, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
      exact ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
    have hlen : indices.length = k := by
      rw [← List.toFinset_card_of_nodup ((Finset.sort_nodup V (· ≤ ·)).filter _), he, hcard]
    exact List.mem_map.mpr ⟨indices, List.mem_sublistsLen.mpr ⟨List.filter_sublist, hlen⟩, he⟩

@[simp] theorem subsetList_length (V : Finset (Fin n)) : (subsetList V).length = 2 ^ V.card := by
  simp [subsetList, List.length_sublists]

@[simp] theorem fixedSubsetList_length (V : Finset (Fin n)) (k : ℕ) :
    (fixedSubsetList V k).length = V.card.choose k := by
  simp [fixedSubsetList]

namespace RepresentationLeaf

/-- Raw leaves retain the three subset choices, including repeated weights. -/
def enumerate (L : RepresentationLeaf (Fin n)) : List (Occurrence (Fin n)) :=
  ((fixedSubsetList L.top L.topCount) ×ˢ (fixedSubsetList L.mixer L.localCount)) ×ˢ
    (subsetList L.background)

theorem enumerate_mem (L : RepresentationLeaf (Fin n)) (x : Occurrence (Fin n)) :
    x ∈ L.enumerate ↔ x ∈ L.occurrences := by
  rcases x with ⟨⟨x, y⟩, z⟩
  simp only [enumerate, List.mem_product, fixedSubsetList_mem, subsetList_mem,
    occurrences, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powerset]

@[simp] theorem enumerate_length (L : RepresentationLeaf (Fin n)) :
    L.enumerate.length = L.occurrences.card := by
  unfold enumerate
  rw [List.length_product, List.length_product, fixedSubsetList_length,
    fixedSubsetList_length, subsetList_length, occurrences_card]

theorem enumerate_toFinset (L : RepresentationLeaf (Fin n)) : L.enumerate.toFinset = L.occurrences := by
  ext x
  simp only [List.mem_toFinset, enumerate_mem]

theorem enumerate_nodup (L : RepresentationLeaf (Fin n)) : L.enumerate.Nodup := by
  rw [← Multiset.coe_nodup]
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change L.enumerate.toFinset.card = L.enumerate.length
  rw [enumerate_toFinset, enumerate_length]

end RepresentationLeaf
end LowSpaceSubsetSum

end OAI
