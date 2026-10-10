import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.EditMetric
import Mathlib

namespace OAI

namespace TreeEdit.BinaryLower

/-- Strictly increasing index selections produce sublists. -/
theorem ofFn_get_sublist {α : Type*} (x : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (hi : StrictMono i) :
    (List.ofFn (fun t => x.get (i t))).Sublist x := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  let f : Fin (List.ofFn (fun t => x.get (i t))).length → Fin x.length :=
    fun t => i ⟨t, by simpa using t.isLt⟩
  have hf : StrictMono f := fun _ _ h => hi h
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro t
  simp [f]

/-- A matching described by two increasing index maps is a common sublist
with exactly as many symbols as matched index pairs. -/
theorem common_sublist_of_strict_matching {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k := by
  refine ⟨List.ofFn (fun t => x.get (i t)), ofFn_get_sublist x i hi, ?_, by simp⟩
  have heq : (fun t => x.get (i t)) = (fun t => y.get (j t)) := funext hlabel
  rw [heq]
  exact ofFn_get_sublist y j hj


/-- Every increasing matching has size at most the longest common subsequence. -/
theorem matching_length_le_lcs {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) : k ≤ lcs x y := by
  obtain ⟨z, hzx, hzy, hz⟩ := common_sublist_of_strict_matching x y i j hi hj hlabel
  rw [← hz]
  exact length_le_lcs hzx hzy

end TreeEdit.BinaryLower

end OAI
