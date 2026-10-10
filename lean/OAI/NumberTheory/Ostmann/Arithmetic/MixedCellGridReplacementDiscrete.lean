import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open PrimeCellReplacement PrimeCellFreezing MixedCellIntegralFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def mixedAssignedLog (N : ι → ℕ) (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η)
    (n : ℕ) (p : AssignedPrimeTuple N lo hi η j) : Option ι → ℝ :=
  Option.elim' (Real.log (n:ℝ)) (assignedTupleLog N lo hi η j p)

theorem mixedAssignedLog_mem (NI : ℕ) (N : ι → ℕ) (loI hiI ηI : ℝ) (lo hi η : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) {n : ℕ}
    (hn : n ∈ assignedIntegerSupport NI loI hiI ηI j.1) (p : AssignedPrimeTuple N lo hi η j.2) :
    mixedAssignedLog N lo hi η j.2 n p ∈
      logRectangle (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
        (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)) := by
  intro i _
  cases i with
  | none => exact ((mem_cellSupport _ _ _ _).mp (Finset.mem_filter.mp hn).1).2.2
  | some i => exact assignedTupleLog_mem N lo hi η j.2 p i (Set.mem_univ _)

theorem exp_mixedAssignedLog (NI : ℕ) (N : ι → ℕ) (loI hiI ηI : ℝ) (lo hi η : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) {n : ℕ}
    (hn : n ∈ assignedIntegerSupport NI loI hiI ηI j.1) (p : AssignedPrimeTuple N lo hi η j.2) :
    (fun i => Real.exp (mixedAssignedLog N lo hi η j.2 n p i)) =
      Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)) := by
  funext i
  cases i with
  | none =>
    apply Real.exp_log
    exact_mod_cast ((mem_cellSupport _ _ _ _).mp (Finset.mem_filter.mp hn).1).2.1
  | some i => exact congrFun (exp_assignedTupleLog N lo hi η j.2 p) i

theorem mixed_assigned_freezing_of_variation (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (hZ : ∀ i, 0 ≤ Z i)
    (hφ0 : ∀ t ∈ Set.Icc (gridPoint loI hiI ηI j.1.val)
      (gridPoint loI hiI ηI (j.1.val+1)), 0 ≤ φ (t-G))
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ)
    (f₀ : ℂ) {v : ℝ}
    (hvar : ∀ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
      ∀ p : AssignedPrimeTuple N lo hi η j.2,
      ‖f (Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)))-f₀‖ ≤ v) :
    ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
      f₀*mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F‖ ≤
      v*mixedAssignedAbsMass NI N M loI hiI ηI G φ lo hi η Z j F := by
  classical
  have heq : mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
      f₀*mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F =
      ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
        ∑ p : AssignedPrimeTuple N lo hi η j.2,
          (((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ)*(assignedTupleWeight N lo hi η Z j.2 p:ℂ)*
            jointUnitTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M)))*
          (f (Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)))-f₀) := by
    simp only [mixedSmoothAssignedTestSum,mixedAssignedTestSum,assignedJointTestSum_tupleWeight,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
        ∑ p : AssignedPrimeTuple N lo hi η j.2,
          ‖(((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ)*(assignedTupleWeight N lo hi η Z j.2 p:ℂ)*
            jointUnitTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M)))*
          (f (Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)))-f₀)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
    _ ≤ ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
        ∑ p : AssignedPrimeTuple N lo hi η j.2,
          v*((Real.exp (-G)*φ (Real.log n-G))*
            (assignedTupleWeight N lo hi η Z j.2 p*
              jointAbsTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M)))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hwI : 0 ≤ Real.exp (-G)*φ (Real.log n-G) :=
        mul_nonneg (Real.exp_pos _).le
          (hφ0 _ ((mem_cellSupport _ _ _ _).mp (Finset.mem_filter.mp hn).1).2.2)
      apply Finset.sum_le_sum
      intro p hp
      have hwP := assignedTupleWeight_nonneg N lo hi η Z hZ j.2 p
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hwI,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hwP]
      calc
        _ ≤ ((Real.exp (-G)*φ (Real.log n-G))*assignedTupleWeight N lo hi η Z j.2 p*
              jointAbsTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M)))*v :=
          mul_le_mul (mul_le_mul_of_nonneg_left (jointUnitTest_norm_le _ _) (mul_nonneg hwI hwP))
            (hvar n hn p) (norm_nonneg _) (mul_nonneg (mul_nonneg hwI hwP) (jointAbsTest_nonneg _ _))
        _ = _ := by ring
    _ = _ := by
      simp only [mixedAssignedAbsMass,assignedAbsMass,Finset.mul_sum]

theorem smooth_mixed_assigned_freezing_bound (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (hZ : ∀ i, 0 ≤ Z i)
    (hφ0 : ∀ t ∈ Set.Icc (gridPoint loI hiI ηI j.1.val)
      (gridPoint loI hiI ηI (j.1.val+1)), 0 ≤ φ (t-G))
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh)
    (hwidthI : gridPoint loI hiI ηI (j.1.val+1)-gridPoint loI hiI ηI j.1.val ≤ mesh)
    (hwidth : ∀ i, boxUpper lo hi η j.2 i-boxLower lo hi η j.2 i ≤ mesh)
    (hf : ∀ z∈logRectangle
      (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
      (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)),
      DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z)
    (hd : ∀ z∈logRectangle
      (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
      (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2)), ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun i => Real.exp (z i)) i t)) 0‖ ≤ D)
    {base : Option ι → ℝ} (hbase : base∈logRectangle
      (Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2))
      (Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2))) :
    ‖mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f-
      f (fun i => Real.exp (base i))*mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F‖ ≤
      ((Fintype.card ι:ℝ)+1)*D*mesh*mixedAssignedAbsMass NI N M loI hiI ηI G φ lo hi η Z j F := by
  apply mixed_assigned_freezing_of_variation NI N loI hiI ηI G φ lo hi η Z j hZ hφ0 F f
  intro n hn p
  have hp := mixedAssignedLog_mem NI N loI hiI ηI lo hi η j hn p
  have hwidth' : ∀ i : Option ι,
      Option.elim' (gridPoint loI hiI ηI (j.1.val+1)) (boxUpper lo hi η j.2) i -
      Option.elim' (gridPoint loI hiI ηI j.1.val) (boxLower lo hi η j.2) i ≤ mesh := by
    intro i
    cases i with
    | none => exact hwidthI
    | some i => exact hwidth i
  have hh := positive_norm_sub_le f _ _ hD hm hf hd hp hbase
    (logRectangle_coordinate_dist_le _ _ hwidth' hp hbase)
  simpa only [exp_mixedAssignedLog NI N loI hiI ηI lo hi η j hn p,
    Fintype.card_option,Nat.cast_add,Nat.cast_one] using hh

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
