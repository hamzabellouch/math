import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.UniformEliminationHeight
import OAI.Analysis.MatrixSigning.Optimization.PivotDescentMachine
import OAI.Analysis.MatrixSigning.Matrices.PivotReplayLoop
import OAI.Analysis.MatrixSigning.Complexity.TerminalWitnessCost
import OAI.Analysis.MatrixSigning.Optimization.EliminationWitnessHeight

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

inductive ControllerReachable {N : ℕ} (A : DenseRatMatrix N) :
    {n : ℕ} → DenseRatMatrix n → PivotHistory n N → Prop
  | initial : ControllerReachable A A (.nil N)
  | descend {n : ℕ} {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
      (previous : ControllerReachable A M h)
      (test : pivotTerminal (DenseRatMatrix.decode M) = none) :
      ControllerReachable A (child M) (.push (DenseRatMatrix.decode M) h)

theorem ControllerReachable.call {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) : DenseEliminationCall A M := by
  induction hr with
  | initial => exact .initial
  | descend _ ht ih => exact ih.uniform_child ht

theorem ControllerReachable.matrix_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    (KS.W08.denseMatrixTape M).length ≤ N*N*(8*KS.W30.inverseBitBound N b+15) := by
  have hp := fun i j => hr.call.entry_parts_size_le b hnum hden i j
  have ht := KS.W08.denseMatrixTape_length_le M (KS.W30.inverseBitBound N b)
    (fun i j => (Nat.size_le.mp (hp i j).1).le)
    (fun i j => (Nat.size_le.mp (hp i j).2).le)
  exact ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hr.call.dimension_le hr.call.dimension_le))

theorem uniform_witness_height {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix n} (hc : DenseEliminationCall A M) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    CommonHeight q (witnessHeightBudget N b n) := by
  have he := denseNegativeWitness_decode n M
  rw [← uniformNegativeWitness_eq, hq] at he
  cases hd : denseNegativeWitness n M with
  | none => simp [hd] at he
  | some y =>
    have hy : decodeRatVector y = q := by simpa [hd] using he
    rw [← hy]
    exact denseNegativeWitness_commonHeight A b hnum hden M hc y hd

theorem commonHeight_vector_tape_length {n E : ℕ} {q : Fin n → ℚ} (h : CommonHeight q E) :
    (KS.W12.RowDot.vectorTape q).length ≤ n*(8*E+15) := by
  have hl (i : Fin n) : KS.W01.ratLength (q i) ≤ 4*E+7 := by
    have hp := h.parts_bound i
    have hh := KS.W01.ratLength_le_of_parts (q i) E E hp.1 hp.2
    omega
  have he : (KS.W12.RowDot.vectorTape q).length =
      ∑ i : Fin n, (2*KS.W01.ratLength (q i)+1) := by
    simp [KS.W12.RowDot.vectorTape,List.length_flatMap,List.sum_ofFn,KS.W01.length_frame,KS.W01.ratLength]
  rw [he]
  calc
    _ ≤ ∑ _i : Fin n, (8*E+15) := Finset.sum_le_sum (fun i _ => by have := hl i; omega)
    _ = _ := by simp

theorem ControllerReachable.witness_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    (KS.W12.RowDot.vectorTape q).length ≤ N*(8*witnessHeightBudget N b N+15) := by
  have hc := uniform_witness_height hr.call b hnum hden q hq
  have he : witnessHeightBudget N b n ≤ witnessHeightBudget N b N := by
    unfold witnessHeightBudget
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hr.call.dimension_le 1)
  exact (commonHeight_vector_tape_length (hc.mono he)).trans (Nat.mul_le_mul_right _ hr.call.dimension_le)

def originalMatrixTapeBound (N b : ℕ) : ℕ := N*N*(8*KS.W30.inverseBitBound N b+15)
def originalWitnessTapeBound (N b : ℕ) : ℕ := N*(8*witnessHeightBudget N b N+15)
def originalFrameBound (N b : ℕ) : ℕ := 4*N+2*originalMatrixTapeBound N b+3

theorem ControllerReachable.history_tape_length {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) :
    (historyTape h).length ≤ h.depth * originalFrameBound N b := by
  induction hr with
  | initial => simp [historyTape,PivotHistory.depth]
  | @descend n M h previous ht ih =>
    have hm := previous.matrix_tape_length b hnum hden
    have hd := previous.call.dimension_le
    have hraw := KS.W19.TerminalWitnessMachine.raw_length_le (n+1)
    have hframe : (savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape M)).length ≤
        originalFrameBound N b := by
      simp only [savedFrame,KS.W01.length_frame,KS.W08.SavedPivotPacket.payload,List.length_append]
      unfold originalFrameBound originalMatrixTapeBound
      omega
    simp only [historyTape,DenseRatMatrix.ofMatrix_decode,List.length_append,PivotHistory.depth]
    nlinarith

end KS.W17.FixedPSD

end

end OAI
