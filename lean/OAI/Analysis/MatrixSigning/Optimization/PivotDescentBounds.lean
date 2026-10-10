import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.PivotDescentMachine
import OAI.Analysis.MatrixSigning.Machines.TerminalInputBounds
import OAI.Analysis.MatrixSigning.Complexity.SchurPolynomialBound

namespace OAI

section

namespace KS.W23.PivotDescentBounds
open KS.W01 KS.W07 KS.W17.FixedPSD KS.W03.MachineCombinators
open KS.W19.TerminalWitnessMachine

def descentCoefficient : ℕ := 3000000000000

def payloadBudget (L : ℕ) : ℕ := descentCoefficient*(L+1)^5

theorem payloadBudget_mono {L K : ℕ} (h : L ≤ K) : payloadBudget L ≤ payloadBudget K :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 5)

theorem child_parts_payload {n : ℕ} (M : DenseRatMatrix (n+1)) (i j : Fin n) :
    (DenseRatMatrix.decode (child M) i j).num.natAbs ≤ 2^(4*(W08.denseMatrixTape M).length+3) ∧
    (DenseRatMatrix.decode (child M) i j).den ≤ 2^(4*(W08.denseMatrixTape M).length+3) := by
  simpa only [child, DenseRatMatrix.decode_ofMatrix] using
    SchurTable.entry_parts_le M (W08.denseMatrixTape M).length
      (fun i j => (entry_parts_le_payload M i j).1)
      (fun i j => (entry_parts_le_payload M i j).2) i j

theorem child_tape_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    (W08.denseMatrixTape (child M)).length ≤ 39*((W08.denseMatrixTape M).length+1)^3 := by
  let L := (W08.denseMatrixTape M).length
  have ht := W08.denseMatrixTape_length_le (child M) (4*L+3)
    (fun i j => (child_parts_payload M i j).1)
    (fun i j => (child_parts_payload M i j).2)
  have hn : n+1 ≤ L := dimension_le_payload M
  have hsq : n*n ≤ (L+1)^2 := by
    have h := Nat.mul_le_mul (show n ≤ L+1 by omega) (show n ≤ L+1 by omega)
    simpa only [pow_two] using h
  have hc : 8*(4*L+3)+15 ≤ 39*(L+1) := by omega
  calc
    (W08.denseMatrixTape (child M)).length ≤ n*n*(8*(4*L+3)+15) := ht
    _ ≤ (L+1)^2*(39*(L+1)) := Nat.mul_le_mul hsq hc
    _ = 39*(L+1)^3 := by ring

theorem schur_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    SchurTableMachine.totalTicks n (W08.denseMatrixTape M).length ≤
      2000000000000*((W08.denseMatrixTape M).length+1)^5 := by
  have hn := dimension_le_payload M
  exact (SchurTableMachine.totalTicks_mono (by omega : n ≤ (W08.denseMatrixTape M).length)
    le_rfl).trans (SchurTableMachine.inputLengthBudget_le_monomial _)

theorem descent_payload_ticks {n : ℕ} (M : DenseRatMatrix (n+1)) :
    descentTicks M (W08.denseMatrixTape M).length ≤ payloadBudget (W08.denseMatrixTape M).length := by
  have hs := schur_payload_ticks M
  have hc := child_tape_payload_bound M
  have hn := dimension_le_payload M
  have hrn := raw_length_le n
  have hrs := raw_length_le (n+1)
  have hp1 : (W08.denseMatrixTape M).length+1 ≤ ((W08.denseMatrixTape M).length+1)^5 :=
    Nat.le_self_pow (by decide) _
  have hp3 : ((W08.denseMatrixTape M).length+1)^3 ≤ ((W08.denseMatrixTape M).length+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold descentTicks payloadBudget descentCoefficient
  omega

theorem fullDescend_payload_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    RunSpec fullDescendProgram (matrixState saved M)
      (matrixState (savedFrame (Computability.encodeNat (n+1)) (W08.denseMatrixTape M) ++ saved) (child M))
      (payloadBudget (W08.denseMatrixTape M).length) :=
  (fullDescend_spec saved M (W08.denseMatrixTape M).length
    (fun i j => (entry_parts_le_payload M i j).1)
    (fun i j => (entry_parts_le_payload M i j).2)).mono (descent_payload_ticks M)

end KS.W23.PivotDescentBounds

end

end OAI
