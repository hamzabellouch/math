import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
open Construction HistorySignedResidues HistoryGiantPriorGrid PrimeCellFreezing

theorem prime_weight_log_bounds (G : ℝ) (p : ℕ) (hp : p ∈ logCellPrimes G)
    (hw : logCellWeight G p ≠ 0) :
    0 < (p : ℝ) ∧ G-1 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ G+1 := by
  have hφ : smoothPartition (Real.log (p : ℝ)-G) ≠ 0 := by
    intro hz
    exact hw (by simp only [logCellWeight, hz, zero_div])
  have hs := smoothPartition_support_subset hφ
  exact ⟨by exact_mod_cast (Finset.mem_filter.mp hp).2.pos,
    by linarith [hs.1], by linarith [hs.2]⟩

theorem integer_weight_log_bounds (G : ℝ) (n : ℕ) (hn : n ∈ integerPivotCell G)
    (hw : externalPivotWeight G n ≠ 0) :
    0 < (n : ℝ) ∧ G-1 ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ G+1 := by
  have hφ : smoothPartition (Real.log (n : ℝ)-G) ≠ 0 := by
    intro hz
    exact hw (by simp only [externalPivotWeight, hz, mul_zero])
  have hs := smoothPartition_support_subset hφ
  exact ⟨by exact_mod_cast (Finset.mem_Ioc.mp hn).1,
    by linarith [hs.1], by linarith [hs.2]⟩

theorem prime_sample_bound {l : ℕ} (d : Decomposition) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (hout : ∀ q ∈ outside, q.Prime) (G A : ℝ) (f : (Bool → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
      ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0)
    (q : ℕ) (hq : q ∈ logCellPrimes G) (hqw : logCellWeight G q ≠ 0) :
    ‖liftedResidueTest (residueTransform d) V outside h k M hd (p,q) *
      f (fun t => if t then (q : ℝ) else (p : ℝ))‖ ≤
      (outside.prod : ℝ)^(2^(l+1))*A := by
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
  exact mul_le_mul (norm_actual_liftedResidueTest_le d V outside h k M hd hout _) hf
    (norm_nonneg _) (by positivity)

theorem mixed_sample_bound {l : ℕ} (d : Decomposition) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (hout : ∀ q ∈ outside, q.Prime) (G A : ℝ) (f : (Option Unit → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
      (Option.elim' (G+1) (fun _ => G+1)), ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (n : ℕ) (hn : n ∈ integerPivotCell G) (hnw : externalPivotWeight G n ≠ 0)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0) :
    ‖liftedResidueTest (residueTransform d) V outside h k M hd (n,p) *
      f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)))‖ ≤
      (outside.prod : ℝ)^(2^(l+1))*A := by
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
  exact mul_le_mul (norm_actual_liftedResidueTest_le d V outside h k M hd hout _) hf
    (norm_nonneg _) (by positivity)

end Ostmann.Arithmetic.HistoryGiantXiPriorReplacement

end

end OAI
