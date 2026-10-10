import OAI.Combinatorics.ContingencyTables.Transport.SignedMarginTranslation
import OAI.Combinatorics.ContingencyTables.Transport.TableReindex

namespace OAI

/-! # The completion shift is invariant under computed tail indexing -/

namespace ContingencyTables.CompletionTranslation
open scoped BigOperators

variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

lemma sum_some_reindex (e : Option I' ≃ Option I) (he : e none=none) (f : Option I → ℤ) :
    (∑ i,f (e (some i)))=∑ i,f (some i) := by
  have h := e.sum_comp f
  simp only [Fintype.sum_option,he] at h
  exact add_left_cancel h

omit [Fintype I] [Fintype I'] in
lemma reindex_some_ne_none (e : Option I' ≃ Option I) (he : e none=none) (i : I') :
    e (some i)≠none := by
  intro h
  have h' := e.injective (h.trans he.symm)
  cases h'

omit [Fintype I] [Fintype I'] in
theorem star_reindex (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none) (R : Option I → ℤ) (P : Option J → ℤ)
    (i : Option I') (j : Option J') :
    star (fun i => R (eI i)) (fun j => P (eJ j)) i j=star R P (eI i) (eJ j) := by
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [star,hI,hJ]
      rw [sum_some_reindex eJ hJ]
    | some j =>
      rcases h : eJ (some j) with _|j'
      · exact False.elim (reindex_some_ne_none eJ hJ j h)
      · simp only [star,hI,h]
  | some i =>
    rcases h : eI (some i) with _|i'
    · exact False.elim (reindex_some_ne_none eI hI i h)
    · cases j with
      | none => simp only [star,h,hJ]
      | some j =>
        rcases h' : eJ (some j) with _|j'
        · exact False.elim (reindex_some_ne_none eJ hJ j h')
        · rfl

omit [Fintype I] [Fintype I'] in
theorem between_reindex (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none)
    (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (i : Option I') (j : Option J') :
    between (fun i => R₀ (eI i)) (fun i => R₁ (eI i))
      (fun j => P₀ (eJ j)) (fun j => P₁ (eJ j)) i j=
      between R₀ R₁ P₀ P₁ (eI i) (eJ j) :=
  star_reindex eI eJ hI hJ (fun i => (R₁ i:ℤ)-R₀ i) (fun j => (P₁ j:ℤ)-P₀ j) i j

theorem translated_nonnegative_reindex (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none)
    (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) (X : Table R₀ P₀) :
    (∀ i j,0 ≤ (((tableReindex eI eJ R₀ P₀) X).val i j:ℤ)+
      between (fun i => R₀ (eI i)) (fun i => R₁ (eI i))
        (fun j => P₀ (eJ j)) (fun j => P₁ (eJ j)) i j) ↔
    ∀ i j,0 ≤ (X.val i j:ℤ)+between R₀ R₁ P₀ P₁ i j := by
  change (∀ i j,0 ≤ (X.val (eI i) (eJ j):ℤ)+
    between (fun i => R₀ (eI i)) (fun i => R₁ (eI i))
      (fun j => P₀ (eJ j)) (fun j => P₁ (eJ j)) i j) ↔ _
  simp only [between_reindex eI eJ hI hJ]
  constructor
  · intro h i j
    simpa only [Equiv.apply_symm_apply] using h (eI.symm i) (eJ.symm j)
  · intro h i j
    exact h (eI i) (eJ j)

end ContingencyTables.CompletionTranslation

end OAI
