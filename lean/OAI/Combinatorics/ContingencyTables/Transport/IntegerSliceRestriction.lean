import OAI.Combinatorics.ContingencyTables.Transport.IntegerSliceReindex

namespace OAI

/-! # Restricting fixed prefix coordinates

A context is fixed before the signed transport starts. Its coordinates
are removed from the transport index set, so leaf cliques cannot move a
hole into that prefix. The remaining removal form is a principal block.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal BalancedBox BinaryContraction

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

omit [Fintype C] [Fintype D] in
lemma removeOne_fixed (c : C → ℕ) (z : D → ℕ) (i : D) :
    removeOne (Sum.elim c z) (.inr i) = Sum.elim c (removeOne z i) := by
  funext t
  rcases t with t | t <;> simp [removeOne]

omit [Fintype C] [Fintype D] in
lemma removeTwo_fixed (c : C → ℕ) (z : D → ℕ) (i j : D) :
    removeTwo (Sum.elim c z) (.inr i) (.inr j) = Sum.elim c (removeTwo z i j) := by
  simp only [removeTwo, removeOne_fixed]

omit [Fintype C] [Fintype D] in
lemma removalMatrix_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (c : C → ℕ) (z : D → ℕ) :
    integerRemovalMatrix (fun x => F (Sum.elim c x)) z =
      (integerRemovalMatrix F (Sum.elim c z)).submatrix Sum.inr Sum.inr := by
  ext i j
  change (if ValidPair z i j then F (Sum.elim c (removeTwo z i j)) else 0) =
    if ValidPair (Sum.elim c z) (.inr i) (.inr j) then
      F (removeTwo (Sum.elim c z) (.inr i) (.inr j)) else 0
  simp only [ValidPair, Sum.elim_inr, Sum.inr.injEq, removeTwo_fixed]
  split_ifs <;> rfl

lemma removalSignature_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (c : C → ℕ) (z : D → ℕ)
    (hs : OnePositiveDirection (integerRemovalMatrix F (Sum.elim c z)).toBilin') :
    OnePositiveDirection (integerRemovalMatrix (fun x => F (Sum.elim c x)) z).toBilin' := by
  rw [removalMatrix_fixed]
  apply (signature_iff _ (matrix_bilin_symm _ (by
    intro i j
    exact integerRemoval_symm F (Sum.elim c z) (.inr i) (.inr j)))).mpr
  apply onePositive_submatrix
  exact (signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm F _))).mp hs

omit [DecidableEq C] [DecidableEq D] in
theorem positiveSlice_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (mC c : C → ℕ) (mD : D → ℕ)
    (R : ℕ) (hc : InBox mC c)
    (hp : PositiveSlice F (Sum.elim mC mD) ((∑ i, c i)+R)) :
    PositiveSlice (fun x => F (Sum.elim c x)) mD R := by
  intro z hz ht
  apply hp
  · intro t
    rcases t with i | i
    · exact hc i
    · exact hz i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ht]

theorem removalSlice_fixed (F : ((C ⊕ D) → ℕ) → ℝ) (mC c : C → ℕ) (mD : D → ℕ)
    (R : ℕ) (hc : InBox mC c)
    (hs : RemovalSlice F (Sum.elim mC mD) ((∑ i, c i)+R)) :
    RemovalSlice (fun x => F (Sum.elim c x)) mD R := by
  intro z hz ht
  apply removalSignature_fixed
  apply hs
  · intro t
    rcases t with i | i
    · exact hc i
    · exact hz i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ht]
    omega

end ContingencyTables.IntegerWeightedTransport

end OAI
