import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeCutoffBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeCutoffNumerics

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Characters.RationalHistory HistoryGiantPriorGrid PrimeCellFreezing

theorem primeCutoff_exp_giant_bounds (G C : ℝ) (m : ℕ)
    (f : (Bool → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ (fun z : Bool → ℝ => f (fun i => Real.exp (z i))) ∧
      ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        (∀ i : Bool, ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (C*((m:ℝ)+1))) ∧
        ‖f (fun i => Real.exp (z i))‖ ≤ Real.exp (C*((m:ℝ)+1))) :
    ContDiff ℝ ∞ (fun z : Bool → ℝ => primeCutoff G f (fun i => Real.exp (z i))) ∧
      ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        (∀ i : Bool, ‖deriv (fun t => primeCutoff G f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp ((C+cutoffCost)*((m:ℝ)+1))) ∧
        ‖primeCutoff G f (fun i => Real.exp (z i))‖ ≤ Real.exp ((C+cutoffCost)*((m:ℝ)+1)) := by
  have hb := primeCutoff_giant_bounds G f (Real.exp_nonneg _) hf
  refine ⟨hb.1,?_⟩
  intro z hz
  refine ⟨fun i => ((hb.2 z hz).1 i).trans (cutoffCost_mul_exp_le C m),?_⟩
  exact ((hb.2 z hz).2).trans (exp_le_cutoff_exp C m)

theorem mixedCutoff_exp_giant_bounds (G C : ℝ) (m : ℕ)
    (f : (Option Unit → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ (fun z : Option Unit → ℝ => f (fun i => Real.exp (z i))) ∧
      ∀ z ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
        (∀ i : Option Unit, ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (C*((m:ℝ)+1))) ∧
        ‖f (fun i => Real.exp (z i))‖ ≤ Real.exp (C*((m:ℝ)+1))) :
    ContDiff ℝ ∞ (fun z : Option Unit → ℝ => mixedGiantPrimeTest G f (fun i => Real.exp (z i))) ∧
      ∀ z ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
        (∀ i : Option Unit, ‖deriv (fun t => mixedGiantPrimeTest G f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp ((C+cutoffCost)*((m:ℝ)+1))) ∧
        ‖mixedGiantPrimeTest G f (fun i => Real.exp (z i))‖ ≤ Real.exp ((C+cutoffCost)*((m:ℝ)+1)) := by
  have hb := mixedCutoff_giant_bounds G f (Real.exp_nonneg _) hf
  refine ⟨hb.1,?_⟩
  intro z hz
  refine ⟨fun i => ((hb.2 z hz).1 i).trans (cutoffCost_mul_exp_le C m),?_⟩
  exact ((hb.2 z hz).2).trans (exp_le_cutoff_exp C m)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
