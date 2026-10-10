import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurTableCorrectness

namespace OAI

section

namespace KS.W07.SchurTableMachine
open scoped BigOperators

theorem scalar_length_le_tape {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    KS.W01.ratLength (DenseRatMatrix.decode M i j) ≤ (KS.W08.denseMatrixTape M).length := by
  rw [KS.W08.denseMatrixTape_length]
  let k := KS.W08.matrixEntryIndex i j
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n*n)))) =>
    Nat.zero_le (2*(KS.W01.encodeRat (DenseRatMatrix.decode M
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).length+1))
    (Finset.mem_univ k)
  have he : finProdFinEquiv.symm k = (i,j) := by
    exact (finProdFinEquiv.symm_apply_apply (i,j))
  rw [he] at h
  dsimp only at h
  unfold KS.W01.ratLength
  omega

theorem dimension_sq_le_tape {n : ℕ} (M : DenseRatMatrix n) :
    n*n ≤ (KS.W08.denseMatrixTape M).length := by
  rw [KS.W08.denseMatrixTape_length]
  calc n*n = ∑ _k : Fin (n*n), (1 : ℕ) := by simp
       _ ≤ _ := by apply Finset.sum_le_sum; intro k hk; omega

theorem totalTicks_mono {n N B C : ℕ} (hn : n≤N) (hB : B≤C) :
    totalTicks n B ≤ totalTicks N C := by
  unfold totalTicks SchurLoopState.rowBudget SchurLoopState.columnBudget SchurCellMachine.cellBudget
  gcongr

def inputLengthBudget (L : ℕ) : ℕ := totalTicks L L

theorem input_length_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    KS.W03.MachineCombinators.RunSpec program (inputState M) (outputState M)
      (inputLengthBudget (KS.W08.denseMatrixTape M).length) := by
  let L := (KS.W08.denseMatrixTape M).length
  have hp (i j : Fin (n+1)) :
      (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^L ∧
      (DenseRatMatrix.decode M i j).den ≤ 2^L := by
    have h := KS.W01.rational_parts_le_two_pow_length (DenseRatMatrix.decode M i j)
    have he := Nat.pow_le_pow_right (by decide : 0<2) (scalar_length_le_tape M i j)
    exact ⟨h.1.trans he,h.2.trans he⟩
  have hn : n≤L := by
    have h := dimension_sq_le_tape M
    have hsq : n ≤ (n+1)*(n+1) := by nlinarith
    exact hsq.trans h
  exact (full_spec M L (fun i j => (hp i j).1) (fun i j => (hp i j).2)).mono
    (totalTicks_mono hn (le_refl L))

end KS.W07.SchurTableMachine

end

end OAI
