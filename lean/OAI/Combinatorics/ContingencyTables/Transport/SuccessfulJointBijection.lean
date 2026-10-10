import OAI.Combinatorics.ContingencyTables.Sampling.OriginalBalancedJoint
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSuccessRatio

namespace OAI

/-! # The literal successful balanced pairs are exactly the original tables -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PaperJoint (r : I → ℕ) (c : J → ℕ) :=
  BalancedJoint (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)

noncomputable def jointTable (r : I → ℕ) (c : J → ℕ) (a : PaperJoint r c) :=
  balancedJointTable (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
    (stateCapacity_small r c) a

abbrev SuccessfulJoint (r : I → ℕ) (c : J → ℕ) :=
  {a : PaperJoint r c // ∀ i j,paperSmall r c i j=false →
    (dimensionAllowance (I := I) (J := J))^12 ≤ (jointTable r c a).val i j}

noncomputable def originalSuccessfulJoint (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    SuccessfulJoint r c := by
  refine ⟨paperOriginalJoint r c X,?_⟩
  intro i j hs
  unfold jointTable
  rw [paperOriginalJoint_projection]
  simp only [paddedOriginal,hs,Bool.false_eq_true,ite_false]
  omega

noncomputable def unpadSuccessfulJoint (r : I → ℕ) (c : J → ℕ)
    (a : SuccessfulJoint r c) : Table r c := by
  let L := (dimensionAllowance (I := I) (J := J))^12
  let P := largePadding (paperLarge r c) L
  let Y := jointTable r c a.val
  have hm : HasMargins Y.val (paddedRows r P) (paddedColumns c P) := by
    dsimp only [P,paperLarge]
    rw [large_padding_rows,large_padding_columns]
    exact Y.property
  exact unpadTable P ⟨Y.val,hm⟩ (by
    intro i j
    cases hs : paperSmall r c i j with
    | false => simpa only [P,paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,
        true_and,hs,ite_true] using a.property i j hs
    | true => simp [P,paperLarge,largePadding,hs])

lemma unpadSuccessfulJoint_val (r : I → ℕ) (c : J → ℕ) (a : SuccessfulJoint r c) (i : I) (j : J) :
    (unpadSuccessfulJoint r c a).val i j=(jointTable r c a.val).val i j-
      largePadding (paperLarge r c) ((dimensionAllowance (I := I) (J := J))^12) i j := rfl

/-- Each success produces exactly one original table, and every original
table has exactly one successful state/completion preimage. -/
noncomputable def successfulJointEquiv (r : I → ℕ) (c : J → ℕ) :
    Table r c ≃ SuccessfulJoint r c where
  toFun := originalSuccessfulJoint r c
  invFun := unpadSuccessfulJoint r c
  left_inv X := by
    apply Subtype.ext
    funext i j
    rw [unpadSuccessfulJoint_val]
    change (jointTable r c (paperOriginalJoint r c X)).val i j-_=X.val i j
    unfold jointTable
    rw [paperOriginalJoint_projection]
    cases hs : paperSmall r c i j <;> simp [paddedOriginal,paperLarge,largePadding,hs]
  right_inv a := by
    apply Subtype.ext
    apply balancedJointTable_injective (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
      (stateCapacity_small r c)
    change jointTable r c (paperOriginalJoint r c (unpadSuccessfulJoint r c a))=jointTable r c a.val
    unfold jointTable at ⊢
    rw [paperOriginalJoint_projection]
    apply Subtype.ext
    funext i j
    change (unpadSuccessfulJoint r c a).val i j+
      (if paperSmall r c i j then 0 else (dimensionAllowance (I := I) (J := J))^12)=_
    rw [unpadSuccessfulJoint_val]
    cases hs : paperSmall r c i j with
    | false =>
      have ha := a.property i j hs
      simpa only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,
        hs,ite_true,Bool.false_eq_true,ite_false,jointTable] using Nat.sub_add_cancel ha
    | true => simp [paperLarge,largePadding,hs,jointTable]

end ContingencyTables.SmallGraphProfiles

end OAI
