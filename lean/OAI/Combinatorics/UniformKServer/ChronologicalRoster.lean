import Mathlib

namespace OAI

noncomputable section

namespace UniformKServer.ChronologicalRoster

section
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

/-- Ages count subsequent chronological insertions, whether or not those
entries have retired. Equal physical centers remain distinct records. -/
def age (S : Finset I) (c : I → X) (r : ℝ) (i : I) : ℕ :=
  (S.filter fun j => i < j ∧ dist (c i) (c j) ≤ 20*r).card

def young (S : Finset I) (c : I → X) (r : ℝ) (A : ℕ) : Finset I :=
  S.filter fun i => age S c r i < A

end

section
open Finset
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

theorem local_age_count (S T : Finset I) (c : I → X) (r : ℝ) (A : ℕ)
    (hTS : T ⊆ S) (hy : ∀ i ∈ T, age S c r i < A)
    (hd : ∀ i ∈ T, ∀ j ∈ T, dist (c i) (c j) ≤ 20*r) : T.card ≤ A
 := by
  by_cases hT : T.Nonempty
  · let m := T.min' hT
    have hm : m ∈ T := Finset.min'_mem T hT
    have hsub : T.erase m ⊆ S.filter (fun j => m < j ∧ dist (c m) (c j) ≤ 20*r) := by
      intro j hj
      have hjT := (Finset.mem_erase.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨hTS hjT,?_,hd m hm j hjT⟩
      exact lt_of_le_of_ne (Finset.min'_le T j hjT) (Ne.symm (Finset.mem_erase.mp hj).1)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hm] at hcard
    have ha := hy m hm
    change _ < A at ha
    unfold age at ha
    omega
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [this]

end
variable {I X : Type*} [LinearOrder I] [MetricSpace X]

theorem age_insert (S : Finset I) (c : I → X) (r : ℝ) (n i : I)
    (hn : ∀ j ∈ S, j < n) (hi : i ∈ S) :
    age (insert n S) c r i = age S c r i + if dist (c i) (c n) ≤ 20*r then 1 else 0 := by
  have hin := hn i hi
  have hnot : n ∉ S := fun h => (lt_irrefl n) (hn n h)
  unfold age
  rw [Finset.filter_insert]
  by_cases hd : dist (c i) (c n) ≤ 20*r
  · rw [ite_eq_left ⟨hin,hd⟩,ite_eq_left hd,Finset.card_insert_of_notMem]
    exact fun h => hnot (Finset.mem_filter.mp h).1
  · simp [hd]

theorem new_age_zero (S : Finset I) (c : I → X) (r : ℝ) (n : I)
    (hn : ∀ j ∈ S, j < n) : age (insert n S) c r n = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj,hnj,_⟩ := Finset.mem_filter.mp hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact (lt_irrefl _) hnj
  · exact (not_lt_of_gt (hn j hj)) hnj

theorem ball_young_count (S : Finset I) (c : I → X) (r d : ℝ) (A : ℕ) (p : X)
    (hd : 2*d ≤ 20*r) :
    ((young S c r A).filter fun i => dist p (c i) ≤ d).card ≤ A := by
  apply local_age_count S _ c r A
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  · intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have ht := dist_triangle (c i) p (c j)
    rw [dist_comm (c i) p] at ht
    linarith

end UniformKServer.ChronologicalRoster

end

end OAI
