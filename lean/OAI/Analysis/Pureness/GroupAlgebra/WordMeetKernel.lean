import OAI.Analysis.Pureness.GroupAlgebra.FreeWordTreeDistance
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
local instance wordMeetKernelDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X

def wordMeetKernel {X : Type*} (n : ℕ) : List X → List X → ℂ
  | [], v => if v.length = n then 1 else 0
  | u, [] => if u.length = n then 1 else 0
  | a :: u, b :: v => (if u.length + v.length + 2 = n then 1 else 0) +
      if a = b then wordMeetKernel n u v else 0

lemma wordMeetKernel_zero {X : Type*} (u v : List X) :
    wordMeetKernel 0 u v = if u = v then 1 else 0 := by
  induction u generalizing v with
  | nil => cases v <;> simp [wordMeetKernel]
  | cons a u ih =>
    cases v with
    | nil => simp [wordMeetKernel]
    | cons b v =>
      by_cases h : a = b
      · subst b; simp [wordMeetKernel, ih]
      · simp [wordMeetKernel, h]

lemma wordMeetKernel_one {X : Type*} (u v : List X) :
    wordMeetKernel 1 u v = if wordTreeDistance u v = 1 then 1 else 0 := by
  induction u generalizing v with
  | nil => cases v <;> simp [wordMeetKernel, wordTreeDistance]
  | cons a u ih =>
    cases v with
    | nil => simp [wordMeetKernel, wordTreeDistance]
    | cons b v =>
      have hn : u.length + v.length + 2 ≠ 1 := by omega
      by_cases h : a = b
      · subst b; simp [wordMeetKernel, wordTreeDistance, hn, ih]
      · simp [wordMeetKernel, wordTreeDistance, h, hn]

theorem wordTree_shell_identity {X : Type*} (n : ℕ) (u v : List X) :
    (if wordTreeDistance u v = n + 2 then (1 : ℂ) else 0) =
      wordMeetKernel (n + 2) u v - wordMeetKernel n u v +
        if u.length + v.length = n then 1 else 0 := by
  induction u generalizing v with
  | nil => cases v <;> simp [wordMeetKernel, wordTreeDistance]
  | cons a u ih =>
    cases v with
    | nil => simp [wordMeetKernel, wordTreeDistance]
    | cons b v =>
      by_cases h : a = b
      · subst b
        have he : (a :: u).length + (a :: v).length = u.length + v.length + 2 := by simp; omega
        simp only [wordTreeDistance, ↓reduceIte, wordMeetKernel, he]
        rw [ih]
        have hn : u.length + v.length + 2 = n + 2 ↔ u.length + v.length = n := by omega
        simp only [hn]
        ring
      · have he : (a :: u).length + (b :: v).length = u.length + v.length + 2 := by simp; omega
        simp only [wordTreeDistance, ite_eq_right h, wordMeetKernel, add_zero, he]
        ring

def wordAncestor {X : Type*} (i : ℕ) (u : List X) : Option (List X) :=
  if i ≤ u.length then some (u.take (u.length - i)) else none

lemma wordAncestor_cons {X : Type*} (i : ℕ) (a : X) (u : List X) :
    wordAncestor i (a :: u) = if i = u.length + 1 then some [] else
      (wordAncestor i u).map (List.cons a) := by
  by_cases hi : i = u.length + 1
  · subst i; simp [wordAncestor]
  · by_cases hl : i ≤ u.length
    · have hl' : i ≤ (a :: u).length := by simp; omega
      have hd : (a :: u).length - i = (u.length - i) + 1 := by simp; omega
      simp only [wordAncestor, ite_eq_right hi, ite_eq_left hl', ite_eq_left hl, hd,
        List.take_succ_cons, Option.map_some]
    · have hl' : ¬ i ≤ (a :: u).length := by simp; omega
      simp only [wordAncestor, ite_eq_right hi, ite_eq_right hl', ite_eq_right hl, Option.map_none]

def wordAncestorPair {X : Type*} (i j : ℕ) (u v : List X) : ℂ :=
  match wordAncestor i u, wordAncestor j v with
  | some s, some t => if s = t then 1 else 0
  | _, _ => 0

lemma wordAncestorPair_cons {X : Type*} (i j : ℕ) (a b : X) (u v : List X) :
    wordAncestorPair i j (a :: u) (b :: v) =
      (if i = u.length + 1 ∧ j = v.length + 1 then 1 else 0) +
      if a = b then wordAncestorPair i j u v else 0 := by
  have hu : wordAncestor (u.length + 1) u = none := by simp [wordAncestor]
  have hv : wordAncestor (v.length + 1) v = none := by simp [wordAncestor]
  unfold wordAncestorPair
  rw [wordAncestor_cons, wordAncestor_cons]
  by_cases hi : i = u.length + 1 <;> by_cases hj : j = v.length + 1
  · subst i; subst j; simp [hu, hv]
  · subst i; simp only [↓reduceIte, hj, hu]; cases wordAncestor j v <;> simp
  · subst j; simp only [↓reduceIte, hi, hv]; cases wordAncestor i u <;> simp
  · simp only [ite_eq_right hj, hi, false_and, ↓reduceIte, zero_add]
    cases wordAncestor i u <;> cases wordAncestor j v <;> simp [List.cons.injEq]
    split_ifs <;> simp_all
end CuntzPureness

end

end OAI
