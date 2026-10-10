import OAI.Combinatorics.ContingencyTables.Rooted.TreeFeasibleMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhysicalNormalizer
import OAI.Combinatorics.ContingencyTables.Model

namespace OAI

/-! # Feasible physical balanced profiles are exactly bounded contingency tables -/

namespace ContingencyTables.CompanionPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalTable (A : Instance I J) (a : Profiles (cellWidth A)) : I → J → ℤ :=
  fun i j => ForestLiteralCount.lower A.T A.d A.b i j+(a (i,j)).val

def Feasible (A : Instance I J) (a : Profiles (cellWidth A)) : Prop :=
  (∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j) ∧
    (∀ i,(∑ j,physicalTable A a i j)=A.r i) ∧
    (∀ j,(∑ i,physicalTable A a i j)=A.c j)

abbrev PhysicalTables (A : Instance I J) := {a : Profiles (cellWidth A) // Feasible A a}

lemma row_nonnegative (A : Instance I J) (i : I) : 0 ≤ A.r i := by
  rw [← A.hXr i]
  exact Finset.sum_nonneg (fun j _ => (A.hX i j).1)

lemma column_nonnegative (A : Instance I J) (j : J) : 0 ≤ A.c j := by
  rw [← A.hXc j]
  exact Finset.sum_nonneg (fun i _ => (A.hX i j).1)

lemma physicalTable_assignment (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) :
    physicalTable A (tableAssignment A Y hY)=Y := by
  funext i j
  have hz : 0 ≤ Y i j-ForestLiteralCount.lower A.T A.d A.b i j := by
    linarith [(hY i j).1,lower_nonpositive A i j]
  simp only [physicalTable,tableAssignment,Int.toNat_of_nonneg hz]
  ring

lemma assignment_physicalTable (A : Instance I J) (a : Profiles (cellWidth A))
    (ha : ∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j) :
    tableAssignment A (physicalTable A a) ha=a := by
  funext c
  apply Fin.ext
  simp only [tableAssignment,physicalTable,add_sub_cancel_left,Int.toNat_natCast]

noncomputable def toBounded (A : Instance I J) (a : PhysicalTables A) :
    BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b := by
  let Y : I → J → ℕ := fun i j => (physicalTable A a.val i j).toNat
  have hy (i : I) (j : J) : (Y i j:ℤ)=physicalTable A a.val i j :=
    Int.toNat_of_nonneg (a.property.1 i j).1
  refine ⟨⟨Y,⟨?_,?_⟩⟩,?_⟩
  · intro i
    have hh : (∑ j,(Y i j:ℤ))=((A.r i).toNat:ℤ) := by
      simp_rw [hy]
      rw [a.property.2.1 i,Int.toNat_of_nonneg (row_nonnegative A i)]
    exact_mod_cast hh
  · intro j
    have hh : (∑ i,(Y i j:ℤ))=((A.c j).toNat:ℤ) := by
      simp_rw [hy]
      rw [a.property.2.2 j,Int.toNat_of_nonneg (column_nonnegative A j)]
    exact_mod_cast hh
  · intro i j
    have hh : (Y i j:ℤ) ≤ A.b i j := by rw [hy]; exact (a.property.1 i j).2
    exact_mod_cast hh

noncomputable def fromBounded (A : Instance I J)
    (X : BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) : PhysicalTables A := by
  let Y : I → J → ℤ := fun i j => X.val.val i j
  have hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j := by
    intro i j
    dsimp only [Y]
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast X.property i j⟩
  refine ⟨tableAssignment A Y hY,?_⟩
  unfold Feasible
  rw [physicalTable_assignment]
  refine ⟨hY,?_,?_⟩
  · intro i
    have hh : (∑ j,Y i j)=((A.r i).toNat:ℤ) := by
      dsimp only [Y]
      exact_mod_cast X.val.property.1 i
    rwa [Int.toNat_of_nonneg (row_nonnegative A i)] at hh
  · intro j
    have hh : (∑ i,Y i j)=((A.c j).toNat:ℤ) := by
      dsimp only [Y]
      exact_mod_cast X.val.property.2 j
    rwa [Int.toNat_of_nonneg (column_nonnegative A j)] at hh

lemma toBounded_integer (A : Instance I J) (a : PhysicalTables A) (i : I) (j : J) :
    ((toBounded A a).val.val i j:ℤ)=physicalTable A a.val i j := by
  change ((physicalTable A a.val i j).toNat:ℤ)=physicalTable A a.val i j
  exact Int.toNat_of_nonneg (a.property.1 i j).1

lemma fromBounded_table (A : Instance I J)
    (X : BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) :
    physicalTable A (fromBounded A X).val=fun i j => (X.val.val i j:ℤ) := by
  unfold fromBounded
  exact physicalTable_assignment _ _ _

lemma physicalTable_injective (A : Instance I J) : Function.Injective (physicalTable A) := by
  intro a a' hh
  funext t
  apply Fin.ext
  have he := congrFun (congrFun hh t.1) t.2
  simp only [physicalTable] at he
  exact_mod_cast (add_left_cancel he)

/-- The terminal feasible-profile count is the original bounded-table
count, with the instance's necessarily nonnegative margins. -/
noncomputable def tablesEquiv (A : Instance I J) :
    PhysicalTables A ≃ BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b where
  toFun := toBounded A
  invFun := fromBounded A
  left_inv a := by
    apply Subtype.ext
    apply physicalTable_injective A
    funext i j
    rw [fromBounded_table]
    exact toBounded_integer A a i j
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    have hh := toBounded_integer A (fromBounded A X) i j
    rw [fromBounded_table] at hh
    dsimp only at hh
    exact_mod_cast hh

theorem cardinality_eq (A : Instance I J) :
    Fintype.card (PhysicalTables A)=
      Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) :=
  Fintype.card_congr (tablesEquiv A)

theorem feasible_weight_one (A : Instance I J) (alpha : ℝ) (a : Profiles (cellWidth A))
    (ha : Feasible A a) :
    ForestPenaltyApplication.physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha (BalancedCellFibres.profile (cellWidth A) a)=1 := by
  have hh := tableAssignment_unit A alpha (physicalTable A a) ha.1 ha.2.1 ha.2.2
  rwa [assignment_physicalTable A a ha.1] at hh

/-- Every original bounded table contributes exactly one unit, so the
actual normalizer always dominates the table count. -/
theorem table_count_le_mass (A : Instance I J) (alpha : ℝ) :
    (Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b):ℝ) ≤
      CompanionPhysicalNormalizer.physicalMass A alpha := by
  have hcount : (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=
      (Fintype.card (PhysicalTables A):ℝ) := by
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [Fintype.card_subtype]
  rw [← cardinality_eq,← hcount]
  unfold CompanionPhysicalNormalizer.physicalMass
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · rw [feasible_weight_one A alpha a ha]
  · exact ForestPenaltyApplication.physicalWeight_nonnegative _ _ _ _ _ _ _ _

end ContingencyTables.CompanionPhysicalTables

end OAI
