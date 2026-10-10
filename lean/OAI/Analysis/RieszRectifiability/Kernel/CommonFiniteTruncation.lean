import Mathlib

namespace OAI

namespace RieszRectifiability

theorem exists_positive_below_finset {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < r i := by
  classical
  revert hr
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, by norm_num, by simp⟩
  | @insert a s _ ih =>
    intro hr
    have ha := hr a (Finset.mem_insert_self a s)
    obtain ⟨δ, hδ, hsmall⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    have hm : 0 < min δ (r a) := lt_min hδ ha
    refine ⟨min δ (r a) / 2, by positivity, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hh := min_le_right δ (r i)
      linarith
    · have hh := min_le_left δ (r a)
      have hsi := hsmall i hi
      linarith

end RieszRectifiability

end OAI
