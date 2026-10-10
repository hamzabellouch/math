import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeMarginal
import OAI.Combinatorics.ContingencyTables.Rooted.TreeFeasibleMass

namespace OAI

/-! # Actual feasible tables contribute unit selected-root fibre mass -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount
open BalancedCellFibres EqualitySoftening
open TreeMarginalSignature (cellWidth tableAssignment tableAssignment_row tableAssignment_column
  tableAssignment_tree_index)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem tableAssignment_unit (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i, (∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) :
    RootedPenalty.physicalWeight A R alpha
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
  have hlines : ∀ g,RootedPenalty.rootFlag R g=false →
      deviation (RootedPenalty.ell A) (RootedPenalty.widths A) A.r A.c
        (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) g=0 :=
    fun g _ => hdev g
  rw [RootedPenalty.exact_eq,ite_eq_left hlines]
  have hp : RootedPenalty.penalty A R
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY))=0 := by
    unfold RootedPenalty.penalty RootedPenalty.rootPenalty RootedPenalty.ell RootedPenalty.widths treePenalty
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
theorem scalar_exact_ge_one_at_table (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) (t : I×J) :
    1 ≤ scalarExact A R alpha t (tableAssignment A Y hY t).val := by
  rw [exact_eq_fibre]
  have hh := Finset.single_le_sum
    (f := fun a : Profiles (cellWidth A) =>
      if a t=tableAssignment A Y hY t then
        RootedPenalty.physicalWeight A R alpha
          (BalancedCellFibres.profile (cellWidth A) a) else 0)
    (fun a _ => by split_ifs; exact RootedPenalty.physicalWeight_nonnegative A R alpha _; exact le_rfl)
    (Finset.mem_univ (tableAssignment A Y hY))
  simp only [ite_true,tableAssignment_unit A R alpha Y hY hr hc] at hh
  apply hh.trans_eq
  unfold fibre
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl

/-- Tight upper-cell attainment supplies the endpoint on the right of
every lower exterior tree value. -/
theorem upper_tree_endpoint (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=(A.b t.1 t.2:ℤ)) :
    1 ≤ scalarExact A R alpha t (10*A.d*A.b t.1 t.2+A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy] at hi
  push_cast at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2+A.b t.1 t.2 := by
    exact_mod_cast (show ((tableAssignment A Y hY t).val:ℤ)=
      ((10*A.d*A.b t.1 t.2+A.b t.1 t.2:ℕ):ℤ) by push_cast; omega)
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A R alpha Y hY hr hc t

/-- Tight lower-cell attainment supplies the endpoint on the left of
every upper exterior tree value. -/
theorem lower_tree_endpoint (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=0) :
    1 ≤ scalarExact A R alpha t (10*A.d*A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy,zero_add] at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2 := by exact_mod_cast hi
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A R alpha Y hY hr hc t

end ContingencyTables.RootedTreeMarginal

end OAI
