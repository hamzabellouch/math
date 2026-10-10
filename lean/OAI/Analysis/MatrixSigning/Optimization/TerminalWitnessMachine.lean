import Mathlib
import OAI.Analysis.MatrixSigning.Machines.TerminalReadStage
import OAI.Analysis.MatrixSigning.Machines.SparseCoefficientStage
import OAI.Analysis.MatrixSigning.Machines.TerminalSparseAssembly

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07 Matrix

def inputState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool := fun i => if i=31 then KS.W08.denseMatrixTape M else
      if i=26 then Computability.encodeNat (n+1) else if i=32 then saved else
      if i=30 then Computability.encodeNat j.val else []

def collected {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool :=
  Function.update (Function.update (Function.update (inputState saved M j) 33
    (Computability.encodeNat j.val)) 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j)))
    20 (KS.W01.encodeRat (DenseRatMatrix.decode M 0 j))

def copyIndex : Program 35 := KS.W15.WireProgram.copyProgram 30 33 16
  (by decide) (by decide) (by decide)
def collect : Program 35 := compose copyIndex
  (compose (TerminalReadStage.program true) (TerminalReadStage.program false))

def collectTicks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ) (j : Fin (n+1)) : ℕ :=
  let s := Function.update (inputState saved M j) 33 (Computability.encodeNat j.val)
  (2*(Computability.encodeNat j.val).length+2) +
    (TerminalReadStage.readTicks M B j j s true +
      TerminalReadStage.readTicks M B 0 j
        (Function.update s 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j))) false)

theorem collect_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) (j : Fin (n+1)) :
    RunSpec collect (inputState saved M j) (collected saved M j) (collectTicks saved M B j) := by
  let s := Function.update (inputState saved M j) 33 (Computability.encodeNat j.val)
  let t := Function.update s 19 (KS.W01.encodeRat (DenseRatMatrix.decode M j j))
  have hc := KS.W15.WireProgram.copy_spec (30 : Fin 35) 33 16 (by decide) (by decide) (by decide)
    (inputState saved M j) rfl rfl
  have hs : TerminalReadStage.WorkClear s := by
    intro i hi
    fin_cases i <;> simp_all [s,inputState]
  have ht : TerminalReadStage.WorkClear t := by
    intro i hi
    fin_cases i <;> simp_all [t,s,inputState]
  have h1 := TerminalReadStage.read_spec M B hnum hden j j s hs rfl rfl true rfl rfl rfl
  have h2 := TerminalReadStage.read_spec M B hnum hden 0 j t ht rfl rfl false rfl rfl rfl
  exact hc.compose (h1.compose h2)

def coefficient {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) : ℚ :=
  SparseScalarNodes.coefficient (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)

def scalarTicks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) : ℕ :=
  SparseCoefficientStage.ticks (collected saved M j)
    (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)

theorem scalar_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    RunSpec SparseCoefficientStage.program (collected saved M j)
      (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j)))
      (scalarTicks saved M j) := by
  have hc : ∀ i : Fin 35, i.val < 16 → collected saved M j i = [] := by
    intro i hi; fin_cases i <;> simp_all [collected,inputState]
  have h := SparseCoefficientStage.full_spec (collected saved M j)
    (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)
    hc rfl rfl rfl rfl rfl rfl rfl rfl
  have he : SparseCoefficientStage.result (collected saved M j)
      (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j) =
      Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j)) := by
    funext i
    fin_cases i <;> simp [SparseCoefficientStage.result,SparseCoefficientStage.cleanupPorts,
      KS.W04.CleanRationalCompare.clearListState,KS.W04.CleanRationalCompare.clearState,
      collected,inputState,coefficient]
  rw [he] at h
  exact h

def program : Program 35 := compose collect
  (compose SparseCoefficientStage.program TerminalSparseAssembly.program)

def outputState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool := fun i => if i=31 then KS.W08.denseMatrixTape M else
      if i=26 then Computability.encodeNat (n+1) else if i=32 then saved else
      if i=23 then KS.W12.RowDot.vectorTape (KS.W17.zeroPivotWitness (DenseRatMatrix.decode M) 0 j) else []

def ticks {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ) (j : Fin (n+1)) : ℕ :=
  collectTicks saved M B j + (scalarTicks saved M j + TerminalSparseAssembly.ticks (n+1) j.val (coefficient M j))

theorem full_spec {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (j : Fin (n+1)) (hj : j ≠ 0) :
    RunSpec program (inputState saved M j) (outputState saved M j) (ticks saved M B j) := by
  have h1 := collect_spec saved M B hnum hden j
  have h2 := scalar_spec saved M j
  have h3 := TerminalSparseAssembly.sparse_spec
    (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j))) j hj (coefficient M j)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have he : Function.update (Function.update (Function.update
      (Function.update (inputState saved M j) 28 (KS.W01.encodeRat (coefficient M j))) 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (TerminalVectorReplace.sparseVector j (coefficient M j))) =
      outputState saved M j := by
    funext i
    fin_cases i <;> simp [outputState,inputState,coefficient,SparseScalarNodes.coefficient,
      TerminalVectorReplace.sparseVector,KS.W17.zeroPivotWitness]
  rw [he] at h3
  exact h1.compose (h2.compose h3)

theorem witness_negative {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin (n+1))
    (hzero : DenseRatMatrix.decode M 0 0 = 0)
    (hnonzero : DenseRatMatrix.decode M 0 j ≠ 0)
    (hsymm : DenseRatMatrix.decode M j 0 = DenseRatMatrix.decode M 0 j) :
    let q := KS.W17.zeroPivotWitness (DenseRatMatrix.decode M) 0 j
    dotProduct q ((DenseRatMatrix.decode M) *ᵥ q) < 0 :=
  KS.W17.zeroPivotWitness_negative (DenseRatMatrix.decode M) 0 j hzero hnonzero hsymm

end KS.W19.TerminalWitnessMachine

end

end OAI
