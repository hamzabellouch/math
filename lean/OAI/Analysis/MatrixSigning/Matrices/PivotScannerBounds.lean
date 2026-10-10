import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowCorrectness
import OAI.Analysis.MatrixSigning.Matrices.PivotDecisionMachine
import OAI.Analysis.MatrixSigning.Machines.TerminalInputBounds

namespace OAI

section

namespace KS.W23.PivotScannerBounds
open KS.W01 KS.W07 KS.W17 KS.W03.MachineCombinators
open KS.W19.TerminalWitnessMachine

theorem classifier_code_length (q : ℚ) : (W06.RationalSignClassifier.outputCode q).length ≤ 1 := by
  by_cases hn : q < 0
  · simp [W06.RationalSignClassifier.outputCode, hn]
  · by_cases hz : q = 0 <;> simp [W06.RationalSignClassifier.outputCode, hn, hz]

theorem classify_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    PivotRowClassify.ticks M (W08.denseMatrixTape M).length j ≤
      2000*((W08.denseMatrixTape M).length+1)^3 := by
  let L := (W08.denseMatrixTape M).length
  have hn : n+1 ≤ L := dimension_le_payload M
  have hj : (Computability.encodeNat j.val).length ≤ L := (raw_length_le j.val).trans (by omega)
  have hd : (Computability.encodeNat (n+1)).length ≤ L := (raw_length_le (n+1)).trans hn
  have he : ratLength (DenseRatMatrix.decode M 0 j) ≤ L := entry_length_le_payload M 0 j
  have hc := classifier_code_length (DenseRatMatrix.decode M 0 j)
  have hp : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  have hsq : (n+2)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hr : 1024*(n+2)^2*(L+1) ≤ 1024*(L+1)^3 := by
    calc
      1024*(n+2)^2*(L+1) ≤ 1024*(L+1)^2*(L+1) :=
        Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul_left 1024 hsq)
      _ = _ := by ring
  change PivotRowClassify.ticks M L j ≤ 2000*(L+1)^3
  unfold PivotRowClassify.ticks
  omega

theorem row_body_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    PivotRowBody.ticks M (W08.denseMatrixTape M).length j ≤
      3000*((W08.denseMatrixTape M).length+1)^3 := by
  have h := classify_payload_bound M j
  have hn := dimension_le_payload M
  have hj := raw_length_le j.val
  have hp : (W08.denseMatrixTape M).length+1 ≤ ((W08.denseMatrixTape M).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  unfold PivotRowBody.ticks
  omega

theorem entry_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) :
    PivotRowLoop.entryTicks M (W08.denseMatrixTape M).length a ≤
      3000*((W08.denseMatrixTape M).length+1)^3 := by
  unfold PivotRowLoop.entryTicks
  split
  · exact row_body_payload_bound M _
  · exact Nat.zero_le _

theorem loop_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    PivotRowLoop.ticks M (W08.denseMatrixTape M).length a k ≤
      k*(1+3000*((W08.denseMatrixTape M).length+1)^3)+1 := by
  induction k generalizing a with
  | zero => simp [PivotRowLoop.ticks]
  | succ k ih =>
      have he := entry_payload_bound M a
      have ht := ih (a+1)
      rw [PivotRowLoop.ticks]
      split <;> nlinarith

theorem initialize_bound (n : ℕ) : PivotRowLoop.initializeTicks n ≤ 30*(n+1) := by
  have hn := raw_length_le n
  have hs := raw_length_le (n+1)
  have hm : max (Computability.encodeNat (n+1)).length 1 ≤ n+1 := max_le hs (by omega)
  unfold PivotRowLoop.initializeTicks SchurDimension.predecessorTicks
  omega

theorem finish_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index
      (PivotRowLoop.outcome M 1 n).remaining ≤ 13*((W08.denseMatrixTape M).length+1) := by
  have ho := PivotRowLoop.outcome_bounds M 1 n
  have hn := dimension_le_payload M
  have hi := raw_length_le (PivotRowLoop.outcome M 1 n).index
  unfold PivotRowLoop.finishTicks
  omega

theorem row_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotDecision.rowTicks M (W08.denseMatrixTape M).length ≤
      10000*((W08.denseMatrixTape M).length+1)^4 := by
  let L := (W08.denseMatrixTape M).length
  have hn : n+1 ≤ L := dimension_le_payload M
  have hi := initialize_bound n
  have hl := loop_payload_bound M 1 n
  have hf := finish_payload_bound M
  have hp : 1 ≤ (L+1)^3 := Nat.one_le_pow' 3 L
  have hm : n*(1+3000*(L+1)^3) ≤ (L+1)*(3001*(L+1)^3) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  have he : (L+1)*(3001*(L+1)^3) = 3001*(L+1)^4 := by ring
  rw [he] at hm
  have hp1 : L+1 ≤ (L+1)^4 := Nat.le_self_pow (by decide) _
  change PivotDecision.rowTicks M L ≤ 10000*(L+1)^4
  unfold PivotDecision.rowTicks
  change PivotRowLoop.ticks M L 1 n ≤ n*(1+3000*(L+1)^3)+1 at hl
  change PivotRowLoop.finishTicks (PivotRowLoop.outcome M 1 n).index
    (PivotRowLoop.outcome M 1 n).remaining ≤ 13*(L+1) at hf
  omega

theorem decision_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    PivotDecision.ticks M (W08.denseMatrixTape M).length ≤
      100000000*((W08.denseMatrixTape M).length+1)^4 := by
  have hc := classify_payload_bound M 0
  have hr := row_payload_bound M
  have hp : ((W08.denseMatrixTape M).length+1)^3 ≤ ((W08.denseMatrixTape M).length+1)^4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1 ≤ ((W08.denseMatrixTape M).length+1)^4 :=
    Nat.one_le_pow' 4 (W08.denseMatrixTape M).length
  unfold PivotDecision.ticks
  split <;> omega

theorem decision_payload_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec PivotDecision.program (PivotRowLoop.initial M) (PivotDecision.result M)
      (100000000*((W08.denseMatrixTape M).length+1)^4) :=
  (PivotDecision.full_spec M (W08.denseMatrixTape M).length
    (fun i j => (entry_parts_le_payload M i j).1)
    (fun i j => (entry_parts_le_payload M i j).2)).mono (decision_payload_ticks M)

end KS.W23.PivotScannerBounds

end

end OAI
