import OAI.Analysis.Pureness.GroupAlgebra.WordMeetKernel
import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupRadialKernel

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators InnerProductSpace lp
local instance wordAncestorFactorizationDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X

lemma sum_diagonal_indicator (m l n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), if i = m ∧ n - i = l then (1 : ℂ) else 0) =
      if m + l = n then 1 else 0 := by
  by_cases hn : m + l = n
  · have hm : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    rw [ite_eq_left hn, Finset.sum_eq_single m]
    · simp [show n - m = l by omega]
    · intro b hb hbm; simp [hbm]
    · exact fun h => (h hm).elim
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h : ¬ (i = m ∧ n - i = l) := by omega
    simp [h]

lemma wordAncestorPair_nil_left {X : Type*} (i j : ℕ) (v : List X) :
    wordAncestorPair i j ([] : List X) v =
      if i = 0 ∧ j = v.length then 1 else 0 := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = v.length
    · subst j; simp [wordAncestorPair, wordAncestor]
    · by_cases hle : j ≤ v.length
      · have ht : v.take (v.length - j) ≠ [] := by
          intro h
          have hh := congrArg List.length h
          simp only [List.length_take, List.length_nil] at hh
          omega
        simp [wordAncestorPair, wordAncestor, hle, hj, Ne.symm ht]
      · simp [wordAncestorPair, wordAncestor, hle, hj]
  · simp [wordAncestorPair, wordAncestor, hi]

lemma wordAncestorPair_symm {X : Type*} (i j : ℕ) (u v : List X) :
    wordAncestorPair i j u v = wordAncestorPair j i v u := by
  unfold wordAncestorPair
  cases wordAncestor i u <;> cases wordAncestor j v <;> simp [eq_comm]

theorem wordMeetKernel_eq_ancestor_sum {X : Type*} (n : ℕ) (u v : List X) :
    wordMeetKernel n u v = ∑ i ∈ Finset.range (n + 1), wordAncestorPair i (n - i) u v := by
  induction u generalizing v with
  | nil =>
    simp only [wordMeetKernel, wordAncestorPair_nil_left]
    rw [sum_diagonal_indicator]
    simp [eq_comm]
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [wordMeetKernel]
      have hp (i : ℕ) : wordAncestorPair i (n-i) (a :: u) ([] : List X) =
          if i = (a :: u).length ∧ n-i = 0 then 1 else 0 := by
        rw [wordAncestorPair_symm i (n-i) (a :: u) [], wordAncestorPair_nil_left]
        simp only [and_comm]
      simp_rw [hp]
      rw [sum_diagonal_indicator]
      simp
    | cons b v =>
      simp_rw [wordAncestorPair_cons, Finset.sum_add_distrib]
      rw [sum_diagonal_indicator]
      have he : u.length + 1 + (v.length + 1) = u.length + v.length + 2 := by omega
      by_cases hab : a = b
      · subst b; simp [wordMeetKernel, he, ih]
      · simp [wordMeetKernel, he, hab]

def wordAncestorVector {X : Type*} (i : ℕ) (u : List X) : ℓ²(List X, ℂ) :=
  match wordAncestor i u with
  | none => 0
  | some t => wordDelta t

lemma wordAncestorVector_norm_le {X : Type*} (i : ℕ) (u : List X) :
    ‖wordAncestorVector i u‖ ≤ 1 := by
  unfold wordAncestorVector
  cases wordAncestor i u with
  | none => simp
  | some t => exact ((wordDelta_orthonormal X).norm_eq_one t).le

lemma wordAncestorVector_inner {X : Type*} (i j : ℕ) (u v : List X) :
    ⟪wordAncestorVector i u, wordAncestorVector j v⟫_ℂ = wordAncestorPair i j u v := by
  unfold wordAncestorVector wordAncestorPair
  cases wordAncestor i u <;> cases wordAncestor j v <;>
    simp [orthonormal_iff_ite.mp (wordDelta_orthonormal X)]

theorem wordMeetKernel_factorization {X : Type*} (n : ℕ) (u v : List X) :
    wordMeetKernel n u v = ∑ i ∈ Finset.range (n + 1),
      ⟪wordAncestorVector i u, wordAncestorVector (n-i) v⟫_ℂ := by
  simp_rw [wordAncestorVector_inner]
  exact wordMeetKernel_eq_ancestor_sum n u v
end CuntzPureness

end

end OAI
