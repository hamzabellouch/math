import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperJointLaw

namespace OAI

/-! # Empty large rectangles have a unique retained completion -/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- When every cell is retained, both views are fixed by the profile. -/
theorem completionFibre_subsingleton (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hsmall : ∀ i j,small i j=true) :
    Subsingleton (CompletionFibre small B r rbar c cbar z) := by
  constructor
  intro X Y
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i j
    exact (X.property.2.2.1 i j (hsmall i j)).1.trans
      (Y.property.2.2.1 i j (hsmall i j)).1.symm
  · funext i j
    exact (X.property.2.2.1 i j (hsmall i j)).2.trans
      (Y.property.2.2.1 i j (hsmall i j)).2.symm

end ContingencyTables.PhysicalCompletionFibres

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

omit [LinearOrder I] [LinearOrder J] in
lemma allSmall_of_no_large_rectangle
    (hempty : IsEmpty (LargeRows r ((dimensionAllowance (I := I) (J := J))^20)) ∨
      IsEmpty (LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))) :
    ∀ i j,paperSmall r c i j=true := by
  intro i j
  have he : r i<(dimensionAllowance (I := I) (J := J))^20 ∨
      c j<(dimensionAllowance (I := I) (J := J))^20 := by
    rcases hempty with hr|hc
    · left
      by_contra h
      exact hr.false ⟨i,by omega⟩
    · right
      by_contra h
      exact hc.false ⟨j,by omega⟩
  simpa only [paperSmall,firstPaperSmall,decide_eq_true_eq] using he

lemma paperFibre_card_allSmall (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) : Fintype.card (PaperFibre r c z)=1 := by
  let : Subsingleton (PaperFibre r c z) := completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
  let : Unique (PaperFibre r c z) := ⟨⟨Classical.choice inferInstance⟩,fun x => Subsingleton.elim x _⟩
  exact Fintype.card_unique

/-- No dense sampler or numerical integral is needed in this branch. -/
lemma stateWeight_allSmall (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) : stateWeight r c z=1 := by
  change hardMarginal _ _ _ _ _ _=1
  rw [hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)]
  exact_mod_cast paperFibre_card_allSmall r c hsmall z

end ContingencyTables.SmallGraphProfiles

end OAI
