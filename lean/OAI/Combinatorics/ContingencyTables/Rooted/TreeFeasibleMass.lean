import OAI.Combinatorics.ContingencyTables.Rooted.TreeMarginalEnumeration

namespace OAI

/-! # Every feasible table contributes one unit to its actual cell fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount
open BalancedCellFibres EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

lemma lower_nonpositive (A : Instance I J) (i : I) (j : J) :
    lower A.T A.d A.b i j ≤ 0 := by
  unfold lower
  split_ifs <;> omega

lemma upper_ge_capacity (A : Instance I J) (i : I) (j : J) :
    (A.b i j:ℤ) ≤ lower A.T A.d A.b i j+width A.T A.d A.b i j := by
  unfold lower width
  split_ifs
  · have hd := A.hd
    have hprod : A.b i j ≤ A.d*A.b i j := by nlinarith
    have hh : ((A.b i j+10*A.d*A.b i j:ℕ):ℤ) ≤ (20*A.d*A.b i j:ℕ) := by
      exact_mod_cast (show A.b i j+10*A.d*A.b i j ≤ 20*A.d*A.b i j by nlinarith)
    push_cast at hh ⊢
    linarith
  · simp

noncomputable def tableAssignment (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) : Profiles (cellWidth A) := fun a =>
  ⟨(Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat,by
    have hlo := lower_nonpositive A a.1 a.2
    have hup := upper_ge_capacity A a.1 a.2
    have hz : 0 ≤ Y a.1 a.2-lower A.T A.d A.b a.1 a.2 := by linarith [(hY a.1 a.2).1]
    have hb : Y a.1 a.2-lower A.T A.d A.b a.1 a.2 ≤ cellWidth A a := by
      dsimp only [cellWidth]
      linarith [(hY a.1 a.2).2]
    have hn : (Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat ≤ cellWidth A a := by
      exact_mod_cast (show ((Y a.1 a.2-lower A.T A.d A.b a.1 a.2).toNat:ℤ) ≤ cellWidth A a by
        rw [Int.toNat_of_nonneg hz]
        exact hb)
    omega⟩

lemma tableAssignment_row (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (i : I) (j : J) :
    physicalRow (lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j=(Y i j:ℝ) := by
  have hz : 0 ≤ Y i j-lower A.T A.d A.b i j := by
    linarith [(hY i j).1,lower_nonpositive A i j]
  simp only [physicalRow,BalancedCellFibres.profile,Bool.false_eq_true,ite_false,tableAssignment]
  have hn : (((Y i j-lower A.T A.d A.b i j).toNat:ℕ):ℝ)=
      (Y i j:ℝ)-(lower A.T A.d A.b i j:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  rw [hn]
  ring

lemma tableAssignment_column (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (i : I) (j : J) :
    physicalColumn (lower A.T A.d A.b) (width A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j=(Y i j:ℝ) := by
  have hk : (tableAssignment A Y hY (i,j)).val ≤ cellWidth A (i,j) :=
    Nat.le_of_lt_succ (tableAssignment A Y hY (i,j)).isLt
  have hh := tableAssignment_row A Y hY i j
  simp only [physicalColumn,BalancedCellFibres.profile,ite_true,Nat.cast_sub hk]
  change (lower A.T A.d A.b i j:ℝ)+(cellWidth A (i,j):ℝ)-
    ((cellWidth A (i,j):ℝ)-((tableAssignment A Y hY (i,j)).val:ℝ))=(Y i j:ℝ)
  change (lower A.T A.d A.b i j:ℝ)+((tableAssignment A Y hY (i,j)).val:ℝ)=(Y i j:ℝ) at hh
  linarith

theorem tableAssignment_unit (A : Instance I J) (alpha : ℝ) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i, (∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) :
    physicalWeight A.T A.b (lower A.T A.d A.b) (width A.T A.d A.b) A.r A.c alpha
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY))=1 := by
  have hdev : ∀ g,deviation (lower A.T A.d A.b) (width A.T A.d A.b) A.r A.c
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) g=0 := by
    intro g
    cases g with
    | inl i =>
      simp only [deviation,Sum.elim_inl]
      simp_rw [tableAssignment_row]
      have hh : (∑ j,(Y i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast hr i
      rw [hh,sub_self]
    | inr j =>
      simp only [deviation,Sum.elim_inr]
      simp_rw [tableAssignment_column]
      have hh : (∑ i,(Y i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast hc j
      rw [hh,sub_self]
  rw [exact_eq,ite_eq_left (fun g _ => hdev g)]
  have hp : penalty A.T A.b (lower A.T A.d A.b) (width A.T A.d A.b) A.r A.c
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY))=0 := by
    unfold penalty rootPenalty treePenalty
    simp only [hdev,abs_zero,ite_self,Finset.sum_const_zero,zero_add]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hy0 : (0:ℝ) ≤ Y i j := by exact_mod_cast (hY i j).1
    have hyb : (Y i j:ℝ) ≤ A.b i j := by exact_mod_cast (hY i j).2
    have hh := tableAssignment_row A Y hY i j
    unfold affineDistance
    simp only [mul_one]
    change (if A.T.Adj (.inl i) (.inr j) then
      max 0 (max (-(physicalRow (lower A.T A.d A.b)
        (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j))
        (physicalRow (lower A.T A.d A.b)
          (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j-A.b i j)) /
        (A.b i j:ℝ) else 0)=0
    rw [hh,max_eq_left (max_le (neg_nonpos.mpr hy0) (sub_nonpos.mpr hyb))]
    simp
  rw [hp,mul_zero,Real.rpow_zero]

/-- A feasible table supplies an actual unit summand at its retained
physical coordinate. No endpoint-mass oracle is assumed. -/
theorem scalar_exact_ge_one_at_table (A : Instance I J) (alpha : ℝ)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) (t : I×J) :
    1 ≤ scalarExact A alpha t (tableAssignment A Y hY t).val := by
  rw [exact_eq_fibre]
  have hh := Finset.single_le_sum
    (f := fun a : Profiles (cellWidth A) =>
      if a t=tableAssignment A Y hY t then
        physicalWeight A.T A.b (lower A.T A.d A.b) (width A.T A.d A.b) A.r A.c alpha
          (BalancedCellFibres.profile (cellWidth A) a) else 0)
    (fun a _ => by split_ifs; exact physicalWeight_nonnegative _ _ _ _ _ _ _ _; exact le_rfl)
    (Finset.mem_univ (tableAssignment A Y hY))
  simp only [ite_true,tableAssignment_unit A alpha Y hY hr hc] at hh
  apply hh.trans_eq
  unfold fibre
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl

lemma tableAssignment_tree_index (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) :
    ((tableAssignment A Y hY t).val:ℤ)=Y t.1 t.2+(10*A.d*A.b t.1 t.2:ℕ) := by
  have hz : 0 ≤ Y t.1 t.2-lower A.T A.d A.b t.1 t.2 := by
    linarith [(hY t.1 t.2).1,lower_nonpositive A t.1 t.2]
  change ((Y t.1 t.2-lower A.T A.d A.b t.1 t.2).toNat:ℤ)=_
  rw [Int.toNat_of_nonneg hz]
  simp only [lower,ht,ite_true,sub_neg_eq_add]

/-- Tight upper-cell attainment supplies the endpoint on the right of
every lower exterior tree value. -/
theorem upper_tree_endpoint (A : Instance I J) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=(A.b t.1 t.2:ℤ)) :
    1 ≤ scalarExact A alpha t (10*A.d*A.b t.1 t.2+A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy] at hi
  push_cast at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2+A.b t.1 t.2 := by
    exact_mod_cast (show ((tableAssignment A Y hY t).val:ℤ)=
      ((10*A.d*A.b t.1 t.2+A.b t.1 t.2:ℕ):ℤ) by push_cast; omega)
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A alpha Y hY hr hc t

/-- Tight lower-cell attainment supplies the endpoint on the left of
every upper exterior tree value. -/
theorem lower_tree_endpoint (A : Instance I J) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=0) :
    1 ≤ scalarExact A alpha t (10*A.d*A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy,zero_add] at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2 := by exact_mod_cast hi
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A alpha Y hY hr hc t

end ContingencyTables.TreeMarginalSignature

end OAI
