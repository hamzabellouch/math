import Mathlib
import OAI.Analysis.MatrixSigning.Realization.RoundedStepRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def isPSD : Realizes matrixObjectCode boolCode
    (fun a : MatrixObject => decide (KS.W17.rationalNegativeWitness a.1 a.2=none)) :=
  ((psdStored.then (lengthList ratCode)).then natIsZero).congr (by
    intro a
    unfold witnessData
    cases hw : KS.W17.rationalNegativeWitness a.1 a.2 with
    | none => rfl
    | some v =>
      have hn := nonempty_witness_dimension a.2 v hw
      simp [hn])

structure WitnessState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  y : Fin n → ℚ

def witnessStateData (a : WitnessState) : PencilData×List ℚ := (pencilData a.B,List.ofFn a.y)
def witnessStateCode (a : WitnessState) := prodCode pencilCode vectorCode (witnessStateData a)
def witnessStateView : Realizes witnessStateCode (prodCode pencilCode vectorCode) witnessStateData :=
  (identity (prodCode pencilCode vectorCode)).reindex witnessStateCode witnessStateData (fun _ => rfl)
def witnessEvaluation : Realizes witnessStateCode matrixObjectCode
    (fun a => (⟨a.m,a.B.eval a.y⟩ : MatrixObject)) :=
  let B := witnessStateView.then (first pencilCode vectorCode)
  let size := B.then ((first matrixCode (listCode matrixCode)).then (lengthList vectorCode))
  let evaluation := witnessStateView.then evalPencil
  (size.both evaluation).changeOutput matrixObjectCode
    (fun a => ⟨a.m,a.B.eval a.y⟩) (by
      intro a
      change prodCode natCode matrixCode ((matrixData a.B.constant).length,
        evalPencilData (pencilData a.B,List.ofFn a.y))=_
      rw [evalPencil_data]
      simp only [matrixData,List.length_ofFn,matrixObjectCode])
def witnessNone : Realizes witnessStateCode boolCode (fun a => decide (a.B.witness a.y=none)) :=
  witnessEvaluation.then isPSD

end CurrentKS.Realization

end

end OAI
