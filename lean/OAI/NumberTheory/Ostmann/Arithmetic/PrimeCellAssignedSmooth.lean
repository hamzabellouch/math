import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionTuples
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeProgression PrimeCellReplacement PrimeCellFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def assignedTupleWeight (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (p : AssignedPrimeTuple N lo hi η j) : ℝ :=
  ∏ i, (Z i*((p i).val:ℝ))⁻¹

def assignedTupleLog (N : ι → ℕ) (lo hi η : ι → ℝ)
    (j : GridBoxIndex lo hi η) (p : AssignedPrimeTuple N lo hi η j) : ι → ℝ :=
  fun i => Real.log ((p i).val:ℝ)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedTupleLog_mem [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (lo hi η : ι → ℝ)
    (j : GridBoxIndex lo hi η) (p : AssignedPrimeTuple N lo hi η j) :
    assignedTupleLog N lo hi η j p ∈ logRectangle (boxLower lo hi η j) (boxUpper lo hi η j) := by
  intro i _
  exact (mem_logPrimeSupport _ _ _ _).mp (Finset.mem_filter.mp (p i).property).1 |>.2.2

omit [Fintype ι] [DecidableEq ι] in
theorem exp_assignedTupleLog [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (lo hi η : ι → ℝ)
    (j : GridBoxIndex lo hi η) (p : AssignedPrimeTuple N lo hi η j) :
    (fun i => Real.exp (assignedTupleLog N lo hi η j p i)) = fun i => ((p i).val:ℝ) := by
  funext i
  apply Real.exp_log
  exact_mod_cast ((mem_logPrimeSupport _ _ _ _).mp (Finset.mem_filter.mp (p i).property).1).2.1.pos

def assignedAbsMass (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) : ℝ :=
  ∑ p : AssignedPrimeTuple N lo hi η j, assignedTupleWeight N lo hi η Z j p*
    jointAbsTest F (fun i => ((p i).val:ZMod M))

def smoothAssignedJointTestSum (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi η Z : ι → ℝ)
    (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∑ p : AssignedPrimeTuple N lo hi η j, (assignedTupleWeight N lo hi η Z j p:ℂ)*
    jointUnitTest F (fun i => ((p i).val:ZMod M))*f (fun i => ((p i).val:ℝ))

omit [DecidableEq ι] in
theorem assignedTupleWeight_nonneg [DecidableEq ι] (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (hZ : ∀ i, 0 ≤ Z i) (j : GridBoxIndex lo hi η) (p : AssignedPrimeTuple N lo hi η j) :
    0 ≤ assignedTupleWeight N lo hi η Z j p :=
  Finset.prod_nonneg fun i _ => inv_nonneg.mpr (mul_nonneg (hZ i) (Nat.cast_nonneg _))

theorem assigned_coefficient_norm_mass_le (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (hZ : ∀ i, 0 ≤ Z i) (j : GridBoxIndex lo hi η) (F : (ι → (ZMod M)ˣ) → ℂ) :
    (∑ p : AssignedPrimeTuple N lo hi η j,
      ‖(assignedTupleWeight N lo hi η Z j p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M))‖) ≤
      assignedAbsMass N M lo hi η Z j F := by
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (assignedTupleWeight_nonneg N lo hi η Z hZ j p)]
  exact mul_le_mul_of_nonneg_left (jointUnitTest_norm_le F _)
    (assignedTupleWeight_nonneg N lo hi η Z hZ j p)

theorem smooth_assigned_freezing_bound (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (hZ : ∀ i, 0 ≤ Z i) (j : GridBoxIndex lo hi η)
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidth : ∀ i, boxUpper lo hi η j i-boxLower lo hi η j i ≤ mesh)
    (hf : ∀ z∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j),
      DifferentiableAt ℝ (fun y => f (fun q => Real.exp (y q))) z)
    (hd : ∀ z∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j),∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base∈logRectangle (boxLower lo hi η j) (boxUpper lo hi η j)) :
    ‖smoothAssignedJointTestSum N M lo hi η Z j F f-
      f (fun q => Real.exp (base q)) *
        ∑ p : AssignedPrimeTuple N lo hi η j,
          (assignedTupleWeight N lo hi η Z j p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M))‖ ≤
      (Fintype.card ι:ℝ)*D*mesh*assignedAbsMass N M lo hi η Z j F := by
  classical
  let c : AssignedPrimeTuple N lo hi η j → ℂ := fun p =>
    (assignedTupleWeight N lo hi η Z j p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M))
  have he := positive_weighted_freezing_bound Finset.univ c f
    (boxLower lo hi η j) (boxUpper lo hi η j) (assignedTupleLog N lo hi η j)
    (fun _ => base) hD hm hf hd (fun p _ => assignedTupleLog_mem N lo hi η j p)
    (fun _ _ => hbase)
    (fun p _ => logRectangle_coordinate_dist_le _ _ hwidth (assignedTupleLog_mem N lo hi η j p) hbase)
  simp_rw [exp_assignedTupleLog] at he
  have hconst : (∑ p : AssignedPrimeTuple N lo hi η j,c p*f (fun q => Real.exp (base q))) =
      f (fun q => Real.exp (base q)) * ∑ p : AssignedPrimeTuple N lo hi η j,c p := by
    rw [← Finset.sum_mul]
    exact mul_comm _ _
  rw [hconst] at he
  exact he.trans (mul_le_mul_of_nonneg_left (assigned_coefficient_norm_mass_le N lo hi η Z hZ j F)
    (by positivity))

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
