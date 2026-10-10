import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotControllerLoop
import OAI.Analysis.MatrixSigning.Machines.ControllerReplayBound
import OAI.Analysis.MatrixSigning.Matrices.PivotScannerBounds

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

theorem unitTicks_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    unitTicks n ≤ 100*(localBits M+1) := by
  have hn := KS.W19.TerminalWitnessMachine.dimension_le_payload M
  have hl := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
  have hone : KS.W19.TerminalVectorReplace.oneFrame.length = 15 := by decide
  have hz := KS.W19.TerminalWitnessMachine.zero_payload_length (n+1)
  unfold unitTicks KS.W19.TerminalZeroVector.ticks
  rw [hone,hz]
  change _ ≤ 100*((KS.W08.denseMatrixTape M).length+1)
  omega

theorem sparseTicks_payload_bound {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (j : Fin (n+1)) :
    KS.W19.TerminalWitnessMachine.ticks saved M (localBits M) j ≤
      1000000000000000000*(localBits M+1)^3 := by
  exact KS.W19.TerminalWitnessMachine.ticks_polynomial saved M (localBits M) (localBits M)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).1)
    (fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).2)
    (KS.W19.TerminalWitnessMachine.dimension_le_payload M) le_rfl j

theorem ControllerReachable.finish_ticks_le {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    finishTicks h M q ≤ originalMatrixTapeBound N b+N+3+(N+1)*originalReplayStepBound N b := by
  have hm := hr.matrix_tape_length b hnum hden
  have hd := hr.call.dimension_le
  have hraw := KS.W19.TerminalWitnessMachine.raw_length_le n
  have hdepth := h.dimension_depth
  have hrestore := hr.restore_ticks_le b hnum hden q hq
  have hmono := Nat.mul_le_mul_right (originalReplayStepBound N b) (show h.depth+1≤N+1 by omega)
  unfold finishTicks originalMatrixTapeBound
  omega

def originalTerminalBound (N b : ℕ) : ℕ :=
  100000000*(originalMatrixTapeBound N b+1)^4+
  1000000000000000000*(originalMatrixTapeBound N b+1)^3+
  100*(originalMatrixTapeBound N b+1)+originalMatrixTapeBound N b+N+10+
  (N+1)*originalReplayStepBound N b

theorem ControllerReachable.terminal_ticks_le {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (ht : pivotTerminal (DenseRatMatrix.decode M) ≠ none) :
    controllerTicks h M ≤ originalTerminalBound N b := by
  have hm : localBits M ≤ originalMatrixTapeBound N b := hr.matrix_tape_length b hnum hden
  have hdec : PivotDecision.ticks M (localBits M) ≤ 100000000*(originalMatrixTapeBound N b+1)^4 := by
    have hwire : (KS.W08.denseMatrixTape M).length ≤ originalMatrixTapeBound N b := hm
    exact (KS.W23.PivotScannerBounds.decision_payload_ticks M).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hwire 1) 4))
  by_cases hn : DenseRatMatrix.decode M 0 0 < 0
  · have hu := (unitTicks_payload_bound M).trans (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hm 1))
    have hq : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) = some (Pi.single 0 1) := by
      simp [uniformNegativeWitness,pivotTerminal,hn]
    have hf := hr.finish_ticks_le b hnum hden (Pi.single 0 1) hq
    simp only [controllerTicks,hn,ite_true]
    unfold originalTerminalBound
    omega
  · by_cases hz : DenseRatMatrix.decode M 0 0 = 0
    · cases hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
      | none => exact (ht (by simp [pivotTerminal,hz,hj])).elim
      | some j =>
        have hs : KS.W19.TerminalWitnessMachine.ticks (historyTape h) M (localBits M) j.succ ≤
            1000000000000000000*(originalMatrixTapeBound N b+1)^3 := by
          exact (sparseTicks_payload_bound (historyTape h) M j.succ).trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
        have hq : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) =
            some (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ) := by
          simp [uniformNegativeWitness,pivotTerminal,hz,hj]
        have hf := hr.finish_ticks_le b hnum hden _ hq
        simp only [controllerTicks,hz,lt_self_iff_false,ite_true,ite_false,hj]
        unfold originalTerminalBound
        omega
    · exact (ht (by simp [pivotTerminal,hn,hz])).elim

end KS.W17.FixedPSD

end

end OAI
