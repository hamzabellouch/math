import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.BinaryEdit.SubsequenceIntersection
import Mathlib.Tactic

namespace OAI

namespace TreeEdit.BinaryLower

/-- Every elementary edit preserves a common subsequence after at most two
unmatched symbols in total. This includes substitutions by the same letter. -/
theorem EditStep.common_subsequence {α : Type*} {x y : List α}
    (h : EditStep x y) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 + 2 * z.length := by
  cases h with
  | insert p s a =>
      refine ⟨p ++ s, List.Sublist.refl _, ?_, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · simp only [List.length_append, List.length_cons]
        omega
  | delete p s a =>
      refine ⟨p ++ s, ?_, List.Sublist.refl _, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · simp only [List.length_append, List.length_cons]
        omega
  | substitute p s a b =>
      refine ⟨p ++ s, ?_, ?_, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons b)
      · simp only [List.length_append, List.length_cons]
        omega

/-- A script of cost `n` has a common subsequence with at most `2*n` unmatched
symbols in its two endpoints. Intermediate words are unrestricted. -/
theorem EditScript.common_subsequence {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 * n + 2 * z.length := by
  induction h with
  | nil x =>
      exact ⟨x, List.Sublist.refl _, List.Sublist.refl _, by omega⟩
  | cons hstep hscript ih =>
      obtain ⟨z, hzx, hzy, hlen⟩ :=
        common_subsequence_compose (EditStep.common_subsequence hstep) ih
      exact ⟨z, hzx, hzy, by omega⟩

/-- The insertion/deletion deficit of a script's endpoints is at most twice
its ordinary unit-edit cost. -/
theorem EditScript.lcs_loss_le {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    x.length + y.length - 2 * lcs x y ≤ 2 * n := by
  obtain ⟨z, hzx, hzy, hlen⟩ := EditScript.common_subsequence h
  have hz : z.length ≤ lcs x y := by
    apply le_csSup
    · refine ⟨x.length, ?_⟩
      rintro k ⟨w, hwx, hwy, rfl⟩
      exact hwx.length_le
    · exact ⟨z, hzx, hzy, rfl⟩
  omega

end TreeEdit.BinaryLower

end OAI
