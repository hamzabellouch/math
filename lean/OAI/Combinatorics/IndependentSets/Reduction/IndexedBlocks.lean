import Mathlib

namespace OAI

namespace LargeIndependentSets.IndexedBlocks

lemma range_blocks {α : Type*} (f : ℕ → ℕ → α) (k : ℕ) (hk : 0<k) (n : ℕ) :
    (List.range (k*n)).map (fun i => f (i/k) (i%k)) =
      (List.range n).flatMap (fun j => (List.range k).map (f j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,List.range_add,List.map_append,ih,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    have hd : (k*n+j)/k=n := by
      rw [Nat.add_comm,Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt hj',Nat.zero_add]
    simp [hd,Nat.mod_eq_of_lt hj']

end LargeIndependentSets.IndexedBlocks

end OAI
