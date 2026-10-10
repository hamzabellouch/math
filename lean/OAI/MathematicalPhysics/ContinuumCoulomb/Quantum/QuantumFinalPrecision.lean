import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryXZPromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteOutputBounds

namespace OAI

/-! Precision for all nine early simulation errors and the subsequent
routing errors, retaining the exact final inverse-polynomial promise gap. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram

def finalPrecision (rounds : ℕ) (c : QMACircuit) : ℕ :=
  60*(rounds+9)*(c.gates.length+1)

theorem finalPrecision_pos (rounds : ℕ) (c : QMACircuit) :
    0 < finalPrecision rounds c := by
  unfold finalPrecision
  positivity

theorem final_error_budget (rounds : ℕ) (c : QMACircuit) :
    ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      1/(60*(c.gates.length+1:ℝ)) := by
  have hr : (rounds:ℝ)+9 ≠ 0 := by positivity
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [finalPrecision,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  field_simp

theorem final_yes_budget (rounds : ℕ) (c : QMACircuit) :
    1/(3*(c.gates.length+1:ℝ))+((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      (xzYesThreshold c:ℝ) := by
  rw [final_error_budget]
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzYesThreshold,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

theorem final_no_budget (rounds : ℕ) (c : QMACircuit) :
    2/(5*(c.gates.length+1:ℝ))-((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      (xzNoThreshold c:ℝ) := by
  rw [final_error_budget]
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzNoThreshold,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

theorem final_accepting (rounds : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (hc : c.WellFormed) {E : ℝ}
    (herr : |E-(qmaOrderedHistoryModel c hT).energy| ≤
      ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ))
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) : E ≤ (xzYesThreshold c:ℝ) := by
  have he := (abs_le.mp herr).2
  have hh := qmaOrderedHistoryModel_yes c hT hc psi hpsi hacc
  rw [← final_yes_budget rounds c]
  linarith

theorem final_rejecting (rounds : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (hc : c.WellFormed) {E : ℝ}
    (herr : |E-(qmaOrderedHistoryModel c hT).energy| ≤
      ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ))
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) : (xzNoThreshold c:ℝ) ≤ E := by
  have he := (abs_le.mp herr).1
  have hh := qmaOrderedHistoryModel_no c hT hc hsound
  rw [← final_no_budget rounds c]
  linarith

theorem final_threshold_gap_bound (c : QMACircuit) {n k : ℕ}
    (hn : 0 < n) (hT : c.gates.length ≤ n) (hk : 6 ≤ k) :
    ((n+1:ℝ)^k)⁻¹ ≤ (xzNoThreshold c:ℝ)-xzYesThreshold c := by
  have hbase : (2:ℝ) ≤ n+1 := by exact_mod_cast (show 2 ≤ n+1 by omega)
  have ht : (c.gates.length+1:ℝ) ≤ n+1 := by exact_mod_cast Nat.add_le_add_right hT 1
  have hp : (32:ℝ) ≤ (n+1:ℝ)^5 := by
    simpa only [show (2:ℝ)^5=32 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hbase 5
  have hd : 30*(c.gates.length+1:ℝ) ≤ (n+1:ℝ)^k := by
    calc
      _ ≤ 32*(n+1:ℝ) := by nlinarith
      _ ≤ (n+1:ℝ)^5*(n+1) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (n+1:ℝ)^6 := (pow_succ _ 5).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ n+1) hk
  have hg : (xzNoThreshold c:ℝ)-xzYesThreshold c = 1/(30*(c.gates.length+1:ℝ)) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (xz_threshold_gap c)
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,Rat.cast_ofNat] using h
  rw [hg,one_div]
  exact inv_anti₀ (by positivity) hd

noncomputable def finalPrecisionProgram (rounds : ℕ) :
    Procedure unaryCode unaryCode (fun t => 60*(rounds+9)*(t+1)) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (60*(rounds+9))).pair
    Procedure.unarySuccessor)

noncomputable def finalRationalPrecisionProgram (rounds : ℕ) :
    Procedure unaryCode ratCode (fun t => (60*(rounds+9)*(t+1):ℕ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (finalPrecisionProgram rounds))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
