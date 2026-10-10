import OAI.Combinatorics.ContingencyTables.Transport.BalancedBox

namespace OAI

/-! # Raw integer removal slices under coordinate bijections -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox BinaryContraction

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

omit [Fintype C] [Fintype D] in
lemma removeOne_reindex (e : C ≃ D) (z : C → ℕ) (i : C) :
    (removeOne z i) ∘ e.symm = removeOne (z ∘ e.symm) (e i) := by
  funext d
  simp only [Function.comp_apply, removeOne]
  by_cases hd : d = e i
  · subst d
    simp
  · have hi : e.symm d ≠ i := by
      intro hi
      apply hd
      simpa only [Equiv.apply_symm_apply] using congrArg e hi
    simp only [hd, hi, ↓reduceIte]

omit [Fintype C] [Fintype D] in
lemma removeTwo_reindex (e : C ≃ D) (z : C → ℕ) (i j : C) :
    (removeTwo z i j) ∘ e.symm = removeTwo (z ∘ e.symm) (e i) (e j) := by
  simp only [removeTwo, removeOne_reindex]

omit [Fintype C] [Fintype D] in
lemma removalMatrix_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ) :
    integerRemovalMatrix (fun x => F (x ∘ e.symm)) z =
      (integerRemovalMatrix F (z ∘ e.symm)).submatrix e e := by
  ext i j
  have hv : ValidPair (z ∘ e.symm) (e i) (e j) ↔ ValidPair z i j := by
    simp [ValidPair]
  change (if ValidPair z i j then F (removeTwo z i j ∘ e.symm) else 0) =
    if ValidPair (z ∘ e.symm) (e i) (e j) then
      F (removeTwo (z ∘ e.symm) (e i) (e j)) else 0
  simp only [hv, removeTwo_reindex]

lemma removalSignature_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (z : C → ℕ)
    (hs : OnePositiveDirection (integerRemovalMatrix F (z ∘ e.symm)).toBilin') :
    OnePositiveDirection (integerRemovalMatrix (fun x => F (x ∘ e.symm)) z).toBilin' := by
  rw [removalMatrix_reindex]
  apply (signature_iff _ (matrix_bilin_symm _ (by
    intro i j
    exact integerRemoval_symm F (z ∘ e.symm) (e i) (e j)))).mpr
  apply onePositive_submatrix
  exact (signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm F _))).mp hs

omit [DecidableEq C] [DecidableEq D] in
lemma positiveSlice_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (m : D → ℕ) (R : ℕ)
    (hF : PositiveSlice F m R) :
    PositiveSlice (fun x => F (x ∘ e.symm)) (m ∘ e) R := by
  intro z hz ht
  apply hF
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hz (e.symm d)
  · have he := e.sum_comp (fun d => z (e.symm d))
    simp only [Equiv.symm_apply_apply] at he
    exact he.symm.trans ht

lemma removalSlice_reindex (e : C ≃ D) (F : (D → ℕ) → ℝ) (m : D → ℕ) (R : ℕ)
    (hF : RemovalSlice F m R) :
    RemovalSlice (fun x => F (x ∘ e.symm)) (m ∘ e) R := by
  intro z hz ht
  apply removalSignature_reindex
  apply hF
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hz (e.symm d)
  · have he := e.sum_comp (fun d => z (e.symm d))
    simp only [Equiv.symm_apply_apply] at he
    exact he.symm.trans ht

end ContingencyTables.IntegerWeightedTransport

end OAI
