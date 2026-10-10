import OAI.Probability.MatroidProphet.Algorithm.Rule

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

@[simp] lemma mem_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) :
    i ∈ groups M d seen ↔ i ∈ listed M d seen := by
  simp [groups]

lemma groups_nodup (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).Nodup :=
  Finset.sort_nodup _ _

lemma groups_sorted (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).SortedLT :=
  Finset.sortedLT_sort _

@[simp] lemma groups_length (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).length = (listed M d seen).card := by
  simp [groups]

lemma groups_get_lt (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i j : Fin (groups M d seen).length) (h : i < j) :
    (groups M d seen).get i < (groups M d seen).get j :=
  groups_sorted M d seen h

lemma groups_get?_idxOf (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) (hi : i ∈ groups M d seen) :
    (groups M d seen)[(groups M d seen).idxOf i]? = some i :=
  List.getElem?_idxOf hi

lemma groups_idxOf_lt_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i j : ℤ)
    (hi : i ∈ groups M d seen) (hj : j ∈ groups M d seen) :
    (groups M d seen).idxOf i < (groups M d seen).idxOf j ↔ i < j := by
  have hii := List.idxOf_lt_length_of_mem hi
  have hjj := List.idxOf_lt_length_of_mem hj
  have h := (groups_sorted M d seen).getElem_lt_getElem_iff (hi := hii) (hj := hjj)
  simpa using h.symm

lemma groups_earlier_key (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) {j h : ℕ} {i : ℤ}
    (hh : (groups M d seen)[h]? = some i) (hjh : j < h) :
    ∃ k, (groups M d seen)[j]? = some k ∧ k < i := by
  obtain ⟨hh', hi⟩ := List.getElem?_eq_some_iff.mp hh
  have hj : j < (groups M d seen).length := hjh.trans hh'
  refine ⟨(groups M d seen)[j], List.getElem?_eq_getElem hj, ?_⟩
  rw [← hi]
  exact (groups_sorted M d seen).getElem_lt_getElem_of_lt hjh

end MatroidProphet.MainAlgorithm

end OAI
