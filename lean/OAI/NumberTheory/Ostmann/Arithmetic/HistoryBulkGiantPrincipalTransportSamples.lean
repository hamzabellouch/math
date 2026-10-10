import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryGiantXiPriorReplacement PrimeCellFreezing

theorem periodic_prime_sample_bound (M : ℕ) (R : ZMod M × ZMod M → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hR : ∀z, ‖R z‖ ≤ B) (G A : ℝ) (f : (Bool → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
      ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0)
    (q : ℕ) (hq : q ∈ logCellPrimes G) (hqw : logCellWeight G q ≠ 0) :
    ‖R (p,q) *
      f (fun t => if t then (q : ℝ) else (p : ℝ))‖ ≤
      B*A := by
  have hpp := prime_weight_log_bounds G p hp hpw
  have hqq := prime_weight_log_bounds G q hq hqw
  have hf : ‖f (fun t => if t then (q : ℝ) else (p : ℝ))‖ ≤ A := by
    have hz : (fun t : Bool => if t then Real.log (q : ℝ) else Real.log (p : ℝ)) ∈
        logRectangle (fun _ => G-1) (fun _ => G+1) := by
      intro i hi
      cases i
      · exact hpp.2
      · exact hqq.2
    have he : (fun i : Bool => Real.exp (if i then Real.log (q : ℝ) else Real.log (p : ℝ))) =
        (fun t => if t then (q : ℝ) else (p : ℝ)) := by
      funext i
      cases i <;> simp only [Bool.false_eq_true, ite_false, ite_true, Real.exp_log hpp.1,
        Real.exp_log hqq.1]
    simpa only [he] using hA _ hz
  rw [norm_mul]
  exact mul_le_mul (hR _) hf (norm_nonneg _) hB

theorem periodic_mixed_sample_bound (M : ℕ) (R : ZMod M × ZMod M → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hR : ∀z, ‖R z‖ ≤ B) (G A : ℝ) (f : (Option Unit → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
      (Option.elim' (G+1) (fun _ => G+1)), ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (n : ℕ) (hn : n ∈ integerPivotCell G) (hnw : externalPivotWeight G n ≠ 0)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0) :
    ‖R (n,p) *
      f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)))‖ ≤
      B*A := by
  have hnn := integer_weight_log_bounds G n hn hnw
  have hpp := prime_weight_log_bounds G p hp hpw
  have hf : ‖f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)))‖ ≤ A := by
    have hz : Option.elim' (Real.log (n : ℝ)) (fun _ : Unit => Real.log (p : ℝ)) ∈
        logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
          (Option.elim' (G+1) (fun _ => G+1)) := by
      intro i hi
      cases i
      · exact hnn.2
      · exact hpp.2
    have he : (fun i => Real.exp (Option.elim' (Real.log (n : ℝ))
        (fun _ : Unit => Real.log (p : ℝ)) i)) =
        Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)) := by
      funext i
      cases i <;> simp only [Option.elim'_none, Option.elim'_some, Real.exp_log hnn.1,
        Real.exp_log hpp.1]
    simpa only [he] using hA _ hz
  rw [norm_mul]
  exact mul_le_mul (hR _) hf (norm_nonneg _) hB

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
