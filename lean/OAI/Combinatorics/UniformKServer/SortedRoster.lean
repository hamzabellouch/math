import Mathlib

namespace OAI

                                   
section

noncomputable section
namespace UniformKServer.SortedRoster
open Finset
open scoped Classical
variable {I : Type*} [LinearOrder I]

theorem sort_filter (S : Finset I) (p : I → Prop) [DecidablePred p] :
    (S.filter p).sort (·≤·)=(S.sort (·≤·)).filter (fun i => decide (p i)) := by
  let l := (S.sort (·≤·)).filter (fun i => decide (p i))
  have he : l.toFinset=S.filter p := by ext i; simp [l]
  rw [←he]
  exact (List.toFinset_sort (·≤·) ((sort_nodup S _).filter _)).mpr
    ((pairwise_sort S _).filter _)

theorem sort_insert_last (S : Finset I) (n : I) (hn : ∀ i∈S, i<n) :
    (insert n S).sort (·≤·)=S.sort (·≤·)++[n] := by
  have hnot : n∉S := fun h => (lt_irrefl n) (hn n h)
  have hnodup : (S.sort (·≤·)++[n]).Nodup := by
    rw [List.nodup_append]
    refine ⟨sort_nodup S _,List.nodup_singleton n,?_⟩
    intro i hi j hj hij
    have hjn : j=n := by simpa using hj
    subst j
    subst i
    exact hnot ((mem_sort _).mp hi)
  have hp : (S.sort (·≤·)++[n]).Pairwise (·≤·) := by
    rw [List.pairwise_append]
    refine ⟨pairwise_sort S _,by simp,?_⟩
    intro i hi j hj
    have hjn : j=n := by simpa using hj
    subst j
    exact (hn i ((mem_sort _).mp hi)).le
  have he : (S.sort (·≤·)++[n]).toFinset=insert n S := by
    ext i
    simp only [List.mem_toFinset,List.mem_append,mem_sort,List.mem_singleton,mem_insert]
    exact or_comm
  rw [←he]
  exact (List.toFinset_sort _ hnodup).mpr hp

end UniformKServer.SortedRoster

end


end

end OAI
