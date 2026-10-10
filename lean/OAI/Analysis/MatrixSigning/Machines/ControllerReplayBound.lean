import Mathlib
import OAI.Analysis.MatrixSigning.Machines.ControllerReachable

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

def originalReplayInputBound (N b : ℕ) : ℕ :=
  originalMatrixTapeBound N b+N+originalWitnessTapeBound N b

def originalReplayStepBound (N b : ℕ) : ℕ :=
  10000000000000000000000000000*(originalReplayInputBound N b+1)^8+
    10*(originalReplayInputBound N b+1)+20

theorem ControllerReachable.restore_ticks_le {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    restoreTicks h q ≤ (h.depth+1)*originalReplayStepBound N b := by
  induction hr with
  | initial =>
    simp only [restoreTicks,PivotHistory.depth,zero_add,one_mul]
    unfold originalReplayStepBound
    omega
  | @descend n M h previous ht ih =>
    have hchild : uniformNegativeWitness n (schurTail (DenseRatMatrix.decode M)) = some q := by
      simpa [child] using hq
    have hparent : uniformNegativeWitness (n+1) (DenseRatMatrix.decode M) =
        some (schurWitnessLift (DenseRatMatrix.decode M) q) := by
      simp [uniformNegativeWitness,ht,hchild]
    have htail := (ControllerReachable.descend previous ht).witness_tape_length b hnum hden q hq
    have hhead := previous.witness_tape_length b hnum hden
      (schurWitnessLift (DenseRatMatrix.decode M) q) hparent
    have hmatrix := previous.matrix_tape_length b hnum hden
    have hdim := previous.call.dimension_le
    have hraw := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
    have hin : KS.W12.StoredWitnessLift.inputLength M q ≤ originalReplayInputBound N b := by
      unfold KS.W12.StoredWitnessLift.inputLength originalReplayInputBound
        originalMatrixTapeBound originalWitnessTapeBound
      omega
    have hwork : KS.W12.StoredWitnessLift.ticks M q ≤
        10000000000000000000000000000*(originalReplayInputBound N b+1)^8 := by
      have hh := KS.W12.StoredWitnessLift.ticks_polynomial M q
      unfold KS.W29.polynomialFuel at hh
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8))
    have hlift : (liftedTape M q).length ≤ originalWitnessTapeBound N b := hhead
    have hstep : 1+(9*(Computability.encodeNat (n+1)).length+3*(KS.W08.denseMatrixTape M).length+7+
        replayTicks M q) ≤ originalReplayStepBound N b := by
      unfold replayTicks originalReplayStepBound originalReplayInputBound
        originalMatrixTapeBound originalWitnessTapeBound at *
      omega
    have hi := ih (schurWitnessLift (DenseRatMatrix.decode M) q) hparent
    simp only [restoreTicks,DenseRatMatrix.ofMatrix_decode,PivotHistory.depth]
    nlinarith

end KS.W17.FixedPSD

end

end OAI
