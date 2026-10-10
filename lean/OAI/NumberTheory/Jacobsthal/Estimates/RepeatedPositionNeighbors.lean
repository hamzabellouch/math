import OAI.NumberTheory.Jacobsthal.Partitions.SortedLabelRepetition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPositionNeighbors


theorem repeated_position_neighbor {α : Type*} {n : ℕ} (f : α → Fin n)
    (pre tail : List α) (p : α)
    (hord : ((pre++p::tail).map f).Pairwise (· ≥ ·))
    (hcount : 2 ≤ ((pre++p::tail).map f).count (f p)) :
    (∃ pre' q,pre=pre'++[q] ∧ f q=f p) ∨ (∃ q tail',tail=q::tail' ∧ f q=f p) := by
  have ho : (pre.map f).Pairwise (· ≥ ·) ∧ ((p::tail).map f).Pairwise (· ≥ ·) ∧
      ∀ a ∈ pre.map f,∀ b ∈ (p::tail).map f,a ≥ b := by
    simpa only [List.map_append,List.pairwise_append] using hord
  by_cases hm : f p ∈ pre.map f
  · have hn : pre ≠ [] := by intro he; simp [he] at hm
    let q := pre.getLast hn
    have hqmem : f q ∈ pre.map f := List.mem_map.mpr ⟨q,List.getLast_mem hn,rfl⟩
    have hqge : f p ≤ f q := ho.2.2 _ hqmem _ (by simp)
    have hqle : f q ≤ f p := by
      have hh := ho.1.rel_getLast hm
      simpa only [List.getLast_map] using hh
    exact Or.inl ⟨pre.dropLast,q,(List.dropLast_append_getLast hn).symm,le_antisymm hqle hqge⟩
  · have hc : 0 < (tail.map f).count (f p) := by
      have hz : (pre.map f).count (f p)=0 := List.count_eq_zero.mpr hm
      simpa [List.map_append,List.count_append,hz] using hcount
    have ht := List.count_pos_iff.mp hc
    cases tail with
    | nil => simp at ht
    | cons q tail =>
      have hqle : f q ≤ f p := (List.pairwise_cons.mp ho.2.1).1 _ (by simp)
      have htail : ((q::tail).map f).Pairwise (· ≥ ·) := (List.pairwise_cons.mp ho.2.1).2
      have hqge : f p ≤ f q := by
        have hh := htail.rel_head ht
        simpa using hh
      exact Or.inr ⟨q,tail,rfl,le_antisymm hqle hqge⟩
end NumberTheoryLean.RepeatedPositionNeighbors


end Erdos970

end OAI
