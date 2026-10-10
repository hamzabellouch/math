import Mathlib
import OAI.Analysis.MatrixSigning.Realization.VectorRealization
import OAI.Analysis.MatrixSigning.Realization.BinaryNaturalRealization
import OAI.Analysis.MatrixSigning.Realization.PSDCleanRoutine

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

lemma fold_append_flatten {α : Type*} (xs : List (List α)) (acc : List α) :
    xs.foldl (fun a b => a++b) acc=acc++xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih,List.append_assoc]

def flattenList {α : Type*} (ea : α → Word) :
    Realizes (listCode (listCode ea)) (listCode ea) List.flatten :=
  (((constant (listCode (listCode ea)) (listCode ea) []).both
    (identity (listCode (listCode ea)))).then (appendList ea).fold).congr (by
      intro xs
      simpa using fold_append_flatten xs [])

lemma matrixData_flatten {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    (matrixData M).flatten=List.ofFn (fun k : Fin (n*n) => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*n+j.val,KS.W08.matrixEntryIndex_lt i j⟩ : Fin (n*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,Equiv.symm_apply_apply]

lemma vector_tape {n : ℕ} (v : Fin n → ℚ) :
    vectorCode (List.ofFn v)=KS.W12.RowDot.vectorTape v := by
  change (List.ofFn v).flatMap (fun x => KS.W01.frame (ratCode x))=
    (List.ofFn (ratCode ∘ v)).flatMap KS.W01.frame
  rw [←List.map_ofFn,List.flatMap_map]

lemma matrixData_tape {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    vectorCode (matrixData M).flatten=KS.W08.denseMatrixTape (KS.W07.DenseRatMatrix.ofMatrix M) := by
  rw [matrixData_flatten,vector_tape]
  simp only [KS.W12.RowDot.vectorTape,KS.W08.denseMatrixTape,KS.W08.denseMatrixPayloads,
    KS.W07.DenseRatMatrix.decode_ofMatrix]

abbrev MatrixObject := Σ n : ℕ,Matrix (Fin n) (Fin n) ℚ

def matrixObjectCode (a : MatrixObject) : Word := prodCode natCode matrixCode (a.1,matrixData a.2)
def witnessData (a : MatrixObject) : List ℚ :=
  (KS.W17.rationalNegativeWitness a.1 a.2).elim [] List.ofFn

def psdStored : Realizes matrixObjectCode vectorCode witnessData := by
  let gen := (first natCode matrixCode).then natToBinary
  let flat := (second natCode matrixCode).then (flattenList ratCode)
  let prep := (gen.both flat).reindex matrixObjectCode (fun a => (a.1,matrixData a.2)) (fun _ => rfl)
  let pre := prep.changeOutput PSDCleanRoutine.input
    (fun a : MatrixObject => ⟨a.1,KS.W07.DenseRatMatrix.ofMatrix a.2⟩) (by
      intro a
      change KS.W01.frame (Computability.encodeNat a.1)++vectorCode (matrixData a.2).flatten=_
      rw [matrixData_tape]
      rfl)
  let raw : Realizes PSDCleanRoutine.input vectorCode
      (fun a => (KS.W17.rationalNegativeWitness a.1 (KS.W07.DenseRatMatrix.decode a.2)).elim [] List.ofFn) := {
    cost := PSDCleanRoutine.ticks
    routine := {
      scratch := PSDCleanRoutine.routine.scratch
      program := PSDCleanRoutine.routine.program
      spec := fun a => by
        have h := PSDCleanRoutine.routine.spec a
        cases he : KS.W17.rationalNegativeWitness a.1 (KS.W07.DenseRatMatrix.decode a.2) with
        | none =>
          simp only [PSDCleanRoutine.output,he,Option.elim_none] at h ⊢
          exact h
        | some v =>
          simpa only [PSDCleanRoutine.output,he,Option.elim_some,vector_tape] using h } }
  exact (pre.then raw).congr (fun a => by simp only [witnessData,KS.W07.DenseRatMatrix.decode_ofMatrix])

end CurrentKS.Realization

end OAI
