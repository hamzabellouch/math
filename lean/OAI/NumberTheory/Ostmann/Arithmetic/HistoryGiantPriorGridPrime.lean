import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion PrimeProgression PrimeCellReplacement
open scoped BigOperators

def primeCutoff (G : ℝ) (f : (Bool → ℝ) → ℂ) (x : Bool → ℝ) : ℂ :=
  (giantCell G (x false) : ℂ) * (giantCell G (x true) : ℂ) * f x

theorem gridMean_pair_eq_tuple (G : ℝ) (E : Finset ℕ) (H : ℕ → ℕ → ℂ) :
    gridMean G E (fun p => gridMean G E (H p)) =
    ∑ x : Bool → {p : ℕ // p ∈ giantPrimeSupport G},
      (((logCellMass G E*((x false).val:ℝ))⁻¹ : ℝ) : ℂ) *
      (((logCellMass G E*((x true).val:ℝ))⁻¹ : ℝ) : ℂ) *
      (smoothPartition (Real.log (x false).val-G) : ℂ) *
      (smoothPartition (Real.log (x true).val-G) : ℂ) *
      H (x false).val (x true).val := by
  classical
  rw [gridMean_eq_closedPrime_subtype]
  simp_rw [gridMean_eq_closedPrime_subtype, Finset.mul_sum]
  let S := {p : ℕ // p ∈ giantPrimeSupport G}
  let f : (Bool → S) → ℂ := fun x =>
    (((logCellMass G E*((x false).val:ℝ))⁻¹ : ℝ) : ℂ) *
    (((logCellMass G E*((x true).val:ℝ))⁻¹ : ℝ) : ℂ) *
    (smoothPartition (Real.log (x false).val-G) : ℂ) *
    (smoothPartition (Real.log (x true).val-G) : ℂ) * H (x false).val (x true).val
  change _ = ∑ x : Bool → S, f x
  rw [←(Equiv.boolArrowEquivProd S).symm.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [f,Equiv.boolArrowEquivProd_symm_apply,Bool.false_eq_true,ite_false,ite_true]
  ring

theorem gridMean_pair_eq_smoothJointTestSum (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (F : (Bool → (ZMod M)ˣ) → ℂ) (f : (Bool → ℝ) → ℂ) :
    gridMean G E (fun p => gridMean G E (fun q =>
      jointUnitTest F (fun t => if t then (q : ZMod M) else (p : ZMod M)) *
        f (fun t => if t then (q : ℝ) else (p : ℝ)))) =
    smoothJointTestSum (fun _ : Bool => giantPrimeCutoff G) M
      (fun _ => G-1) (fun _ => G+1) (fun _ => logCellMass G E) F (primeCutoff G f) := by
  classical
  rw [gridMean_pair_eq_tuple]
  unfold smoothJointTestSum
  apply Finset.sum_congr rfl
  intro x _
  have hx (t : Bool) : 0 < ((x t).val : ℝ) := by
    exact_mod_cast ((mem_logPrimeSupport _ _ _ _).mp (x t).property).2.1.pos
  have hr : (fun t : Bool => if t then ((x true).val : ℝ) else ((x false).val : ℝ)) =
      (fun t => ((x t).val : ℝ)) := by funext t; cases t <;> rfl
  have hz : (fun t : Bool => if t then ((x true).val : ZMod M) else ((x false).val : ZMod M)) =
      (fun t => ((x t).val : ZMod M)) := by funext t; cases t <;> rfl
  simp only [primeCutoff,tupleWeight,Fintype.prod_bool,Complex.ofReal_mul,hr,hz,
    giantCell,ite_eq_left (hx false),ite_eq_left (hx true)]
  ring

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
