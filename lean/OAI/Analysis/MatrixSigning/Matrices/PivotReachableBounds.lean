import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotControllerLoop
import OAI.Analysis.MatrixSigning.Machines.ControllerReachable
import OAI.Analysis.MatrixSigning.Matrices.PivotScannerBounds
import OAI.Analysis.MatrixSigning.Optimization.PivotDescentBounds

namespace OAI

section

namespace KS.W23.PivotReachableBounds
open KS.W07 KS.W17 KS.W17.FixedPSD KS.W19.TerminalWitnessMachine

def stepTicks {n : ℕ} (M : DenseRatMatrix (n+1)) : ℕ :=
  1+(PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1))

def stepCoefficient : ℕ := PivotDescentBounds.descentCoefficient+100000000+2

def stepBudget (L : ℕ) : ℕ := stepCoefficient*(L+1)^5

theorem stepBudget_mono {L K : ℕ} (h : L ≤ K) : stepBudget L ≤ stepBudget K :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 5)

theorem step_payload_bound {n : ℕ} (M : DenseRatMatrix (n+1)) :
    stepTicks M ≤ stepBudget (localBits M) := by
  have hd := PivotDescentBounds.descent_payload_ticks M
  have hc := PivotScannerBounds.decision_payload_ticks M
  have hp : ((KS.W08.denseMatrixTape M).length+1)^4 ≤ ((KS.W08.denseMatrixTape M).length+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1 ≤ ((KS.W08.denseMatrixTape M).length+1)^5 :=
    Nat.one_le_pow' 5 (KS.W08.denseMatrixTape M).length
  unfold stepTicks stepBudget stepCoefficient localBits
  unfold PivotDescentBounds.payloadBudget at hd
  rw [Nat.add_mul, Nat.add_mul]
  omega

theorem reachable_step_bound {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
    (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    stepTicks M ≤ stepBudget (originalMatrixTapeBound N b) :=
  (step_payload_bound M).trans (stepBudget_mono (hr.matrix_tape_length b hnum hden))

theorem original_tape_bound_monomial {N L : ℕ} (hN : N ≤ L) :
    originalMatrixTapeBound N L ≤ 55*(L+1)^6 := by
  have hsq := Nat.mul_le_mul hN hN
  have hi := KS.W30.inverseBitBound_mono_dim L hN
  calc
    originalMatrixTapeBound N L ≤ L*L*(8*KS.W30.inverseBitBound L L+15) := by
      exact Nat.mul_le_mul hsq (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hi) 15)
    _ ≤ 55*(L+1)^6 := by
      unfold KS.W30.inverseBitBound
      ring_nf
      omega

def originalStepCoefficient : ℕ := stepCoefficient*56^5

theorem reachable_step_original_payload {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
    (hr : ControllerReachable A M h) :
    stepTicks M ≤ originalStepCoefficient*((KS.W08.denseMatrixTape A).length+1)^30 := by
  let L := (KS.W08.denseMatrixTape A).length
  have ht := reachable_step_bound hr L
    (fun i j => (entry_parts_le_payload A i j).1)
    (fun i j => (entry_parts_le_payload A i j).2)
  have hM := original_tape_bound_monomial (dimension_le_payload A)
  change originalMatrixTapeBound N L ≤ 55 * (L + 1) ^ 6 at hM
  have hp : 1 ≤ (L+1)^6 := Nat.one_le_pow' 6 L
  have hT : originalMatrixTapeBound N L+1 ≤ 56*(L+1)^6 := by omega
  calc
    stepTicks M ≤ stepBudget (originalMatrixTapeBound N L) := ht
    _ ≤ stepCoefficient*(56*(L+1)^6)^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 5)
    _ = originalStepCoefficient*(L+1)^30 := by
      unfold originalStepCoefficient
      rw [mul_pow, ← pow_mul]
      ring

theorem controller_descent_step_bound {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
    (hr : ControllerReachable A M h) :
    1+(PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1)) ≤
      originalStepCoefficient*((KS.W08.denseMatrixTape A).length+1)^30 :=
  reachable_step_original_payload hr

end KS.W23.PivotReachableBounds

end

end OAI
