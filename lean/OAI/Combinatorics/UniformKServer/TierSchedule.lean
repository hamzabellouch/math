import Mathlib
import OAI.Combinatorics.UniformKServer.ChronologicalBound

namespace OAI

                                   
section

/-! The literal insertion schedule. It inspects chronological ages, not
realized lifetimes, and is defined before any radius or lifetime tape. -/
noncomputable section
namespace UniformKServer.TierSchedule
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type*} [MetricSpace X] {N : ℕ}

def trigger (r : ℝ) (K : ℕ) (S : Finset (Fin N)) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) : Prop :=
  q n ∧ ¬∃ i ∈ young S c r K, dist (c n) (c i) ≤ r/2

def run (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) : ℕ → Finset (Fin N)
  | 0 => ∅
  | t+1 => if ht : t<N then
      if trigger r K (run r K q c t) q c ⟨t,ht⟩ then insert ⟨t,ht⟩ (run r K q c t) else run r K q c t
    else run r K q c t

theorem index_lt (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ)
    (i : Fin N) (hi : i ∈ run r K q c t) : i.val<t := by
  induction t with
  | zero => simp only [run,notMem_empty] at hi
  | succ t ih =>
    simp only [run] at hi
    split_ifs at hi with ht hn
    · rcases mem_insert.mp hi with rfl|hi
      · exact Nat.lt_succ_self t
      · exact Nat.lt_succ_of_lt (ih hi)
    · exact Nat.lt_succ_of_lt (ih hi)
    · exact Nat.lt_succ_of_lt (ih hi)

theorem increasing (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    run r K q c t ⊆ run r K q c (t+1) := by
  rw [run]
  split_ifs
  · exact subset_insert _ _
  · exact Subset.rfl
  · exact Subset.rfl

theorem chronological_coverage (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (hK : 0<K)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) (hq : q n) :
    ∃ i ∈ young (run r K q c (n.val+1)) c r K, dist (c n) (c i) ≤ r/2 := by
  have ht := n.isLt
  rw [run,dite_eq_left ht]
  by_cases hn : trigger r K (run r K q c n.val) q c n
  · rw [ite_eq_left hn]
    refine ⟨n,mem_filter.mpr ⟨mem_insert_self _ _,?_⟩,?_⟩
    · rw [new_age_zero]
      · exact hK
      · intro i hi
        exact index_lt r K q c n.val i hi
    · rw [dist_self]; positivity
  · rw [ite_eq_right hn]
    exact Classical.not_not.mp (fun hh => hn ⟨hq,hh⟩)

theorem young_next_subset (r : ℝ) (K A : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) :
    young (run r K q c (n.val+1)) c r A ⊆ insert n (young (run r K q c n.val) c r A) := by
  rw [run,dite_eq_left n.isLt]
  split_ifs
  · exact young_insert_subset _ _ _ _ _
  · exact subset_insert _ _

end UniformKServer.TierSchedule

end


end

end OAI
