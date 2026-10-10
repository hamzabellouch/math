import Mathlib
import OAI.Combinatorics.UniformKServer.ChronologicalRoster

namespace OAI

                                         
section

noncomputable section
namespace UniformKServer.ChronologicalRoster
open Finset
open scoped Classical
variable {I X : Type*} [LinearOrder I] [Fintype X] [MetricSpace X]

theorem global_young_count (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 ≤ r) (A : ℕ) :
    (young S c r A).card ≤ Fintype.card X*A := by
  have hf (x : X) : ((young S c r A).filter (fun i => c i=x)).card ≤ A := by
    apply local_age_count S _ c r A
    · intro i hi
      exact (mem_filter.mp (mem_filter.mp hi).1).1
    · intro i hi
      exact (mem_filter.mp (mem_filter.mp hi).1).2
    · intro i hi j hj
      rw [(mem_filter.mp hi).2,(mem_filter.mp hj).2,dist_self]
      positivity
  have hc := sum_le_sum (s:=univ) (fun x _ => hf x)
  rw [←card_eq_sum_card_fiberwise (f:=c) (s:=young S c r A) (t:=univ) (fun _ _ => mem_univ _)] at hc
  simpa using hc

omit [Fintype X] in
theorem age_mono {S T : Finset I} (hST : S ⊆ T) (c : I → X) (r : ℝ) (i : I) :
    age S c r i ≤ age T c r i := by
  apply card_le_card
  intro j hj
  obtain ⟨hj,hj'⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hST hj,hj'⟩

omit [Fintype X] in
theorem young_insert_subset (S : Finset I) (c : I → X) (r : ℝ) (A : ℕ) (n : I) :
    young (insert n S) c r A ⊆ insert n (young S c r A) := by
  intro i hi
  obtain ⟨hi,ha⟩ := mem_filter.mp hi
  rcases mem_insert.mp hi with he|hi
  · exact mem_insert.mpr (Or.inl he)
  · exact mem_insert_of_mem (mem_filter.mpr ⟨hi,lt_of_le_of_lt (age_mono (subset_insert n S) c r i) ha⟩)

end UniformKServer.ChronologicalRoster

end


end

end OAI
