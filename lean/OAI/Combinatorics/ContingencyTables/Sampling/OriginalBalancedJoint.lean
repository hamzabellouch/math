import OAI.Combinatorics.ContingencyTables.Transport.BalancedJointConstruction
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallChain

namespace OAI

/-! # Every original table supplies its literal balanced padded joint object -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paddedOriginal (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) :
    Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L) :=
  ⟨fun i j => X.val i j+if small i j then 0 else L,by
    constructor
    · intro i
      rw [Finset.sum_add_distrib,X.property.1]
      dsimp only
      unfold rowLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      cases small i j <;> simp
    · intro j
      rw [Finset.sum_add_distrib,X.property.2]
      dsimp only
      unfold columnLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      cases small i j <;> simp⟩

omit [LinearOrder I] [LinearOrder J] in
lemma paddedOriginal_small_rows (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (i : I) :
    smallRow small (paddedOriginal small L X).val i ≤ r i := by
  calc
    _ = ∑ j,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      cases hs : small i j <;> simp [paddedOriginal,hs]
    _ ≤ ∑ j,X.val i j := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := X.property.1 i

omit [LinearOrder I] [LinearOrder J] in
lemma paddedOriginal_small_columns (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (j : J) :
    smallColumnView small (paddedOriginal small L X).val j ≤ c j := by
  calc
    _ = ∑ i,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hs : small i j <;> simp [paddedOriginal,hs]
    _ ≤ ∑ i,X.val i j := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = _ := X.property.2 j

omit [LinearOrder I] [LinearOrder J] in
lemma original_small_entry_le (r : I → ℕ) (c : J → ℕ) (U : ℕ) (X : Table r c)
    (i : I) (j : J) (hs : firstPaperSmall r c U i j=true) : X.val i j ≤ U := by
  have hh : r i<U ∨ c j<U := by simpa only [firstPaperSmall,decide_eq_true_eq] using hs
  rcases hh with hr|hc
  · exact (entry_le_row X.property i j).trans (Nat.le_of_lt hr)
  · have hcol : X.val i j ≤ c j := by
      rw [← X.property.2 j]
      exact Finset.single_le_sum (f := fun i => X.val i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hcol.trans (Nat.le_of_lt hc)

noncomputable def paperOriginalJoint (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    BalancedJoint (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20) := by
  let d := dimensionAllowance (I := I) (J := J)
  let small := paperSmall r c
  let Y := paddedOriginal small (d^12) X
  have hR := paddedOriginal_small_rows small (d^12) X
  have hC := paddedOriginal_small_columns small (d^12) X
  refine jointOfTable small (stateCapacity r c) r c (d^12) (d^20)
    (stateCapacity_small r c) Y ?_ hR hC ?_
  · intro i j hs
    change X.val i j+(if small i j then 0 else d^12) ≤ d^20
    simpa only [hs,ite_true,Nat.add_zero] using original_small_entry_le r c (d^20) X i j hs
  · intro i j _
    exact paper_residual_capacity r c d (d^12) (d^20) dimension_le_allowance ⟨Y,hR,hC⟩ i j

lemma paperOriginalJoint_projection (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    balancedJointTable (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
      (stateCapacity_small r c) (paperOriginalJoint r c X)=
        paddedOriginal (paperSmall r c) ((dimensionAllowance (I := I) (J := J))^12) X := by
  apply Subtype.ext
  rfl

end ContingencyTables.SmallGraphProfiles

end OAI
