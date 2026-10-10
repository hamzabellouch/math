import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeFeasibleMass
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalNormalizer
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhysicalTables

namespace OAI

/-! # Feasible physical tables retain unit mass for the selected roots -/

namespace ContingencyTables.RootedPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres
open CompanionPhysicalTables (Feasible PhysicalTables physicalTable assignment_physicalTable cardinality_eq)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem feasible_weight_one (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (a : Profiles (cellWidth A))
    (ha : Feasible A a) :
    RootedPenalty.physicalWeight A R alpha (BalancedCellFibres.profile (cellWidth A) a)=1 := by
  have hh := RootedTreeMarginal.tableAssignment_unit A R alpha (physicalTable A a) ha.1 ha.2.1 ha.2.2
  rwa [assignment_physicalTable A a ha.1] at hh

/-- Every original bounded table contributes exactly one unit, so the
actual normalizer always dominates the table count. -/
theorem table_count_le_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    (Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b):ℝ) ≤
      RootedPhysicalNormalizer.physicalMass A R alpha := by
  have hcount : (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=
      (Fintype.card (PhysicalTables A):ℝ) := by
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [Fintype.card_subtype]
  rw [← cardinality_eq,← hcount]
  unfold RootedPhysicalNormalizer.physicalMass
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · rw [feasible_weight_one A R alpha a ha]
  · exact RootedPenalty.physicalWeight_nonnegative A R alpha _

end ContingencyTables.RootedPhysicalTables

end OAI
