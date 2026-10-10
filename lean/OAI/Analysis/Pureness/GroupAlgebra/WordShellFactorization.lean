import OAI.Analysis.Pureness.GroupAlgebra.WordAncestorFactorization

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace lp
local instance wordShellFactorizationDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X

lemma wordTreeDistance_eq_zero_iff {X : Type*} (u v : List X) :
    wordTreeDistance u v = 0 ↔ u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp [wordTreeDistance]
  | cons a u ih =>
    cases v with
    | nil => simp [wordTreeDistance]
    | cons b v => by_cases h : a = b <;> simp [wordTreeDistance, h, ih]

def wordLengthVector {X : Type*} (i : ℕ) (u : List X) : ℓ²(List X, ℂ) :=
  if u.length = i then wordDelta [] else 0

lemma wordLengthVector_norm_le {X : Type*} (i : ℕ) (u : List X) :
    ‖wordLengthVector i u‖ ≤ 1 := by
  unfold wordLengthVector
  split_ifs
  · exact ((wordDelta_orthonormal X).norm_eq_one []).le
  · simp

lemma wordLengthVector_inner {X : Type*} (i j : ℕ) (u v : List X) :
    ⟪wordLengthVector i u, wordLengthVector j v⟫_ℂ =
      if u.length = i ∧ v.length = j then 1 else 0 := by
  unfold wordLengthVector
  split_ifs <;> simp_all [(wordDelta_orthonormal X).norm_eq_one]

abbrev WordShellIndex (n : ℕ) := Fin (n + 1) ⊕ (Fin (n - 1) ⊕ Fin (n - 1))

def wordShellSign (n : ℕ) : WordShellIndex n → ℂ
  | .inl _ => 1
  | .inr (.inl _) => -1
  | .inr (.inr _) => 1

def wordShellLeft {X : Type*} (n : ℕ) : WordShellIndex n → List X → ℓ²(List X, ℂ)
  | .inl i => wordAncestorVector i.val
  | .inr (.inl i) => wordAncestorVector i.val
  | .inr (.inr i) => wordLengthVector i.val

def wordShellRight {X : Type*} (n : ℕ) : WordShellIndex n → List X → ℓ²(List X, ℂ)
  | .inl i => wordAncestorVector (n - i.val)
  | .inr (.inl i) => wordAncestorVector (n - 2 - i.val)
  | .inr (.inr i) => wordLengthVector (n - 2 - i.val)

lemma wordShellSign_norm (n : ℕ) (i : WordShellIndex n) : ‖wordShellSign n i‖ ≤ 1 := by
  rcases i with i | i
  · simp [wordShellSign]
  · rcases i with i | i <;> simp [wordShellSign]

lemma wordShellLeft_norm {X : Type*} (n : ℕ) (i : WordShellIndex n) (u : List X) :
    ‖wordShellLeft n i u‖ ≤ 1 := by
  rcases i with i | i
  · exact wordAncestorVector_norm_le _ _
  · rcases i with i | i
    · exact wordAncestorVector_norm_le _ _
    · exact wordLengthVector_norm_le _ _

lemma wordShellRight_norm {X : Type*} (n : ℕ) (i : WordShellIndex n) (u : List X) :
    ‖wordShellRight n i u‖ ≤ 1 := by
  rcases i with i | i
  · exact wordAncestorVector_norm_le _ _
  · rcases i with i | i
    · exact wordAncestorVector_norm_le _ _
    · exact wordLengthVector_norm_le _ _

theorem wordShell_factorization {X : Type*} (n : ℕ) (u v : List X) :
    (if wordTreeDistance u v = n then (1 : ℂ) else 0) =
      ∑ i : WordShellIndex n, wordShellSign n i * ⟪wordShellLeft n i u, wordShellRight n i v⟫_ℂ := by
  simp only [Fintype.sum_sum_type, wordShellSign, wordShellLeft, wordShellRight,
    one_mul, neg_one_mul]
  cases n with
  | zero =>
    simpa [wordTreeDistance_eq_zero_iff, wordMeetKernel_zero] using
      (wordMeetKernel_factorization 0 u v)
  | succ n =>
    cases n with
    | zero =>
      simpa [wordMeetKernel_one, ← Fin.sum_univ_eq_sum_range] using
        (wordMeetKernel_factorization 1 u v)
    | succ n =>
      have hn : n + 1 + 1 - 1 = n + 1 := by omega
      have hn' : n + 1 + 1 - 2 = n := by omega
      simp only [hn', Finset.sum_neg_distrib]
      have hA : wordMeetKernel (n+2) u v = ∑ i : Fin (n+3),
          ⟪wordAncestorVector i.val u, wordAncestorVector (n+2-i.val) v⟫_ℂ := by
        simpa only [← Fin.sum_univ_eq_sum_range, Nat.add_assoc] using wordMeetKernel_factorization (n+2) u v
      have hB : wordMeetKernel n u v = ∑ i : Fin (n+1),
          ⟪wordAncestorVector i.val u, wordAncestorVector (n-i.val) v⟫_ℂ := by
        simpa only [← Fin.sum_univ_eq_sum_range] using wordMeetKernel_factorization n u v
      have hC : (∑ i : Fin (n+1), ⟪wordLengthVector i.val u, wordLengthVector (n-i.val) v⟫_ℂ) =
          if u.length + v.length = n then 1 else 0 := by
        simp only [wordLengthVector_inner]
        simpa only [← Fin.sum_univ_eq_sum_range, eq_comm] using sum_diagonal_indicator u.length v.length n
      change (if wordTreeDistance u v = n+2 then (1 : ℂ) else 0) = _
      have hB' : wordMeetKernel n u v = ∑ i : Fin (n+1+1-1),
          ⟪wordAncestorVector i.val u, wordAncestorVector (n-i.val) v⟫_ℂ :=
        hB.trans (Fin.sum_congr' (fun i : Fin (n+1) =>
          ⟪wordAncestorVector i.val u, wordAncestorVector (n-i.val) v⟫_ℂ) hn).symm
      have hC' : (∑ i : Fin (n+1+1-1), ⟪wordLengthVector i.val u, wordLengthVector (n-i.val) v⟫_ℂ) =
          if u.length + v.length = n then 1 else 0 :=
        (Fin.sum_congr' (fun i : Fin (n+1) =>
          ⟪wordLengthVector i.val u, wordLengthVector (n-i.val) v⟫_ℂ) hn).trans hC
      rw [← hA, ← hB', hC']
      simpa only [sub_eq_add_neg, add_assoc] using wordTree_shell_identity n u v
end CuntzPureness

end

end OAI
