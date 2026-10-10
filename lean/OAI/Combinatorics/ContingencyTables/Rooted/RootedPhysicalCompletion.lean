import OAI.Combinatorics.ContingencyTables.Rooted.RootedAffine
import OAI.Combinatorics.ContingencyTables.Rooted.ForestPhysicalCompletion

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def solved (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) : I → J → ℤ :=
  table A.T S (rowResidual A.small A.T A.r x free)
    (columnResidual A.small A.T A.c q free)

noncomputable def completed (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if A.T.Adj (.inl i) (.inr j) then solved A S x q free i j else free i j

lemma solved_supported (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) (h : ¬A.T.Adj (.inl i) (.inr j)) :
    solved A S x q free i j=0 := table_supported A.T S _ _ i j h

lemma row_pointwise (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) :
    (if A.small i j then x i j else completed A S x q free i j)=
      solved A S x q free i j+fixedRow A.small A.T x free i j := by
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true,fixedRow,add_zero]
  · simp only [completed,ht,ite_false,solved_supported A S x q free i j ht,zero_add,fixedRow]

lemma column_pointwise (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (j : J) :
    (if A.small i j then q i j else completed A S x q free i j)=
      solved A S x q free i j+fixedColumn A.small A.T q free i j := by
  by_cases ht : A.T.Adj (.inl i) (.inr j)
  · have hs : A.small i j=false := A.hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true,fixedColumn,add_zero]
  · simp only [completed,ht,ite_false,solved_supported A S x q free i j ht,zero_add,fixedColumn]

lemma row_completed_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (i : I) (hi : Sum.inl i≠S.root (.inl i)) :
    (∑ j,if A.small i j then x i j else completed A S x q free i j)=A.r i := by
  simp_rw [row_pointwise]
  rw [Finset.sum_add_distrib]
  have he : (∑ j,solved A S x q free i j)=rowResidual A.small A.T A.r x free i :=
    table_row A.small A.T S A.hTG _ _ i hi
  rw [he,rowResidual]
  exact sub_add_cancel _ _

lemma column_completed_sum (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (j : J) (hj : Sum.inr j≠S.root (.inr j)) :
    (∑ i,if A.small i j then q i j else completed A S x q free i j)=A.c j := by
  simp_rw [column_pointwise]
  rw [Finset.sum_add_distrib]
  have he : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j :=
    table_column A.small A.T S A.hTG _ _ j hj
  rw [he,columnResidual]
  exact sub_add_cancel _ _

/-- The cut-defined coefficients evaluate the actual integral solution
for this root convention, including every unbalanced small profile. -/
theorem solved_eq_affine (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A S x q free t.val.1 t.val.2:ℝ)=
      affineTree A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A S x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A S t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A S x q free i hi
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self]) (by
      intro j hj
      have hc := column_completed_sum A S x q free j hj
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self])
  have hz : z t.val.1 t.val.2=(solved A S x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.RootedPhysicalCompletion

end OAI
