import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.TerminalWitnessCost

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W07 KS.W01

theorem entry_length_le_payload {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    ratLength (DenseRatMatrix.decode M i j) ≤ (KS.W08.denseMatrixTape M).length := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n*n)))) =>
      Nat.zero_le (2*(encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2)).length+1))
    (Finset.mem_univ (finProdFinEquiv (i,j)))
  rw [← KS.W08.denseMatrixTape_length] at h
  simp only [Equiv.symm_apply_apply] at h
  change ratLength (DenseRatMatrix.decode M i j) ≤ _
  dsimp only [ratLength]
  omega

theorem dimension_le_payload {n : ℕ} (M : DenseRatMatrix n) :
    n ≤ (KS.W08.denseMatrixTape M).length := by
  have h : n*n ≤ (KS.W08.denseMatrixTape M).length := by
    rw [KS.W08.denseMatrixTape_length]
    calc
      n*n = ∑ _k : Fin (n*n), (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)
  exact (Nat.le_mul_self n).trans h

theorem entry_parts_le_payload {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^(KS.W08.denseMatrixTape M).length ∧
      (DenseRatMatrix.decode M i j).den ≤ 2^(KS.W08.denseMatrixTape M).length := by
  obtain ⟨hn,hd⟩ := rational_parts_le_two_pow_length (DenseRatMatrix.decode M i j)
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (entry_length_le_payload M i j)
  exact ⟨hn.trans hp,hd.trans hp⟩

theorem payload_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1))
    (j : Fin (n+1)) (hj : j ≠ 0) :
    KS.W03.MachineCombinators.RunSpec program (inputState saved M j) (outputState saved M j)
      (1000000000000000000*((KS.W08.denseMatrixTape M).length+1)^3) := by
  let L := (KS.W08.denseMatrixTape M).length
  have hn := fun i j => (entry_parts_le_payload M i j).1
  have hd := fun i j => (entry_parts_le_payload M i j).2
  exact (full_spec saved M L hn hd j hj).mono
    (ticks_polynomial saved M L L hn hd (dimension_le_payload M) le_rfl j)

theorem unit_payload_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    KS.W03.MachineCombinators.RunSpec TerminalVectorReplace.unitProgram (inputState saved M 0)
      (Function.update (inputState saved M 0) 23
        (KS.W12.RowDot.vectorTape (Pi.single (0 : Fin (n+1)) (1 : ℚ))))
      (100*((KS.W08.denseMatrixTape M).length+1)) := by
  have h := TerminalVectorReplace.unit_spec (inputState saved M 0) (n+1) (by omega)
    rfl rfl rfl rfl rfl rfl rfl
  rw [TerminalVectorReplace.unit_tape] at h
  apply h.mono
  have hn := dimension_le_payload M
  have hl := raw_length_le (n+1)
  have hone : TerminalVectorReplace.oneFrame.length = 15 := by decide
  rw [zero_payload_length,hone]
  unfold TerminalZeroVector.ticks
  omega

end KS.W19.TerminalWitnessMachine

end

end OAI
