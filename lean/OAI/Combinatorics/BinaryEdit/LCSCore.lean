import Mathlib.Data.List.Sublists
import Mathlib.Tactic

namespace OAI

/-!
Supporting common-subsequence facts for the edit-distance preliminaries.
These lemmas concern ordinary ordered sublists, not contiguous substrings.
-/
namespace TreeEdit.BinaryLower

/-- Two sublists of one word have a common sublist whose deficit is at most
    the sum of their deficits in that word. -/
theorem common_sublist_lower_bound {α : Type*} {u v w : List α}
    (hu : u.Sublist w) (hv : v.Sublist w) :
    ∃ z : List α, z.Sublist u ∧ z.Sublist v ∧
      u.length + v.length ≤ w.length + z.length := by
  induction w generalizing u v with
  | nil =>
      have hu' : u = [] := List.sublist_nil.mp hu
      have hv' : v = [] := List.sublist_nil.mp hv
      subst u
      subst v
      exact ⟨[], .refl _, .refl _, le_rfl⟩
  | cons a w ih =>
      rcases List.sublist_cons_iff.mp hu with huSkip | ⟨u', rfl, huTail⟩
      · rcases List.sublist_cons_iff.mp hv with hvSkip | ⟨v', rfl, hvTail⟩
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huSkip hvSkip
          refine ⟨z, hzu, hzv, ?_⟩
          simp only [List.length_cons]
          omega
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huSkip hvTail
          refine ⟨z, hzu, hzv.cons a, ?_⟩
          simp only [List.length_cons]
          omega
      · rcases List.sublist_cons_iff.mp hv with hvSkip | ⟨v', rfl, hvTail⟩
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huTail hvSkip
          refine ⟨z, hzu.cons a, hzv, ?_⟩
          simp only [List.length_cons]
          omega
        · obtain ⟨z, hzu, hzv, hz⟩ := ih huTail hvTail
          refine ⟨a :: z, hzu.cons_cons a, hzv.cons_cons a, ?_⟩
          simp only [List.length_cons]
          omega

/-- Deleting at most `k` positions from a word destroys at most `k`
    positions of any selected subsequence. -/
theorem sublist_survives_deletions {α : Type*} {u v w : List α} {k : ℕ}
    (hu : u.Sublist w) (hv : v.Sublist w)
    (hk : w.length ≤ v.length + k) :
    ∃ z : List α, z.Sublist u ∧ z.Sublist v ∧ u.length ≤ z.length + k := by
  obtain ⟨z, hzu, hzv, hz⟩ := common_sublist_lower_bound hu hv
  exact ⟨z, hzu, hzv, by omega⟩

end TreeEdit.BinaryLower

end OAI
