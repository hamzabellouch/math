import Mathlib
import OAI.Analysis.MatrixSigning.Realization.StoredPSDRealization
import OAI.Analysis.MatrixSigning.Optimization.RealVector
import OAI.Analysis.MatrixSigning.Realization.PencilArrayRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

abbrev StepParameters := ℚ×ℚ
abbrev stepParametersCode := prodCode ratCode ratCode
abbrev UpdateData := StepParameters×(List ℚ×List ℚ)
abbrev updateCode := prodCode stepParametersCode (prodCode vectorCode vectorCode)

def roundedUpdateValue (p : UpdateData) : List ℚ :=
  (zipDefault (fun q : ℚ×ℚ => q.1-q.2) 0 0
    (p.2.1,p.2.2.map (fun a => (p.1.1/(p.2.2.map abs).sum)*a))).map
      (fun q => RationalSDP.roundScalar p.1.2 q)

def roundedUpdate : Realizes updateCode vectorCode roundedUpdateValue :=
  let pars := first stepParametersCode (prodCode vectorCode vectorCode)
  let step := pars.then (first ratCode ratCode)
  let mesh := pars.then (second ratCode ratCode)
  let vectors := second stepParametersCode (prodCode vectorCode vectorCode)
  let y := vectors.then (first vectorCode vectorCode)
  let a := vectors.then (second vectorCode vectorCode)
  let norm := a.then l1Rationals
  let scale := ((step.div norm).both a).then vectorScale
  let moved := (y.both scale).then ((ratOp .sub).zipWith 0 0)
  (mesh.both moved).then roundScalar.mapCtx

lemma roundedUpdate_ofFn {n : ℕ} (step mesh : ℚ) (y a : Fin n → ℚ) :
    roundedUpdateValue ((step,mesh),(List.ofFn y,List.ofFn a))=
      List.ofFn (RationalSDP.roundVector mesh (fun i => y i-step*a i/RationalSDP.l1 a)) := by
  unfold roundedUpdateValue
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn]
  rw [zipDefault_ofFn]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  congr 2
  simp only [RationalSDP.l1]
  ring

structure PencilState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  step : ℚ
  mesh : ℚ
  y : Fin n → ℚ

abbrev pencilStateDataCode := prodCode pencilCode (prodCode stepParametersCode vectorCode)
def pencilStateData (s : PencilState) : PencilData×(StepParameters×List ℚ) :=
  (pencilData s.B,((s.step,s.mesh),List.ofFn s.y))
def pencilStateCode (s : PencilState) : Word := pencilStateDataCode (pencilStateData s)

def stateView : Realizes pencilStateCode pencilStateDataCode pencilStateData :=
  (identity pencilStateDataCode).reindex pencilStateCode pencilStateData (fun _ => rfl)

def statePencil : Realizes pencilStateCode pencilCode (fun s => pencilData s.B) :=
  stateView.then (first pencilCode (prodCode stepParametersCode vectorCode))
def stateParameters : Realizes pencilStateCode stepParametersCode (fun s => (s.step,s.mesh)) :=
  stateView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (first stepParametersCode vectorCode))
def stateY : Realizes pencilStateCode vectorCode (fun s => List.ofFn s.y) :=
  stateView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (second stepParametersCode vectorCode))

def stateWitness : Realizes pencilStateCode vectorCode
    (fun s => (s.B.witness s.y).elim [] List.ofFn) := by
  let evaluation := (statePencil.both stateY).then evalPencil
  let dim := statePencil.then ((first matrixCode (listCode matrixCode)).then (lengthList vectorCode))
  let prep := (dim.both evaluation).changeOutput matrixObjectCode
    (fun s : PencilState => ⟨s.m,s.B.eval s.y⟩) (by
      intro s
      change prodCode natCode matrixCode ((matrixData s.B.constant).length,
        evalPencilData (pencilData s.B,List.ofFn s.y))=_
      rw [evalPencil_data]
      simp only [matrixData,List.length_ofFn,matrixObjectCode])
  exact prep.then psdStored

lemma nonempty_witness_dimension {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ)
    (v : Fin m → ℚ) (h : KS.W17.rationalNegativeWitness m M=some v) : m≠0 := by
  cases m with
  | zero => simp only [KS.W17.rationalNegativeWitness] at h;cases h
  | succ m => omega

def stateNextVector : Realizes pencilStateCode vectorCode
    (fun s => List.ofFn (s.B.next s.step s.mesh s.y)) := by
  let witness := stateWitness
  let isNone := witness.then ((lengthList ratCode).then natIsZero)
  let normal := (statePencil.both witness).then normalPencil
  let moved := (stateParameters.both (stateY.both normal)).then roundedUpdate
  refine (isNone.ite stateY moved).congr ?_
  intro s
  change (if decide (((s.B.witness s.y).elim [] List.ofFn).length=0) then List.ofFn s.y else
    roundedUpdateValue ((s.step,s.mesh),(List.ofFn s.y,
      normalData (pencilData s.B,(s.B.witness s.y).elim [] List.ofFn))))=_
  cases hw : s.B.witness s.y with
  | none => simp [RationalSDP.Pencil.next,hw]
  | some v =>
    have hm := nonempty_witness_dimension (s.B.eval s.y) v hw
    simp only [Option.elim_some,List.length_ofFn,hm,decide_false,Bool.false_eq_true,↓reduceIte,
      normalPencil_data,roundedUpdate_ofFn,RationalSDP.Pencil.next,hw]

def PencilState.next (s : PencilState) : PencilState :=
  { s with y := s.B.next s.step s.mesh s.y }

def pencilNext : Realizes pencilStateCode pencilStateCode PencilState.next :=
  (statePencil.both (stateParameters.both stateNextVector)).changeOutput pencilStateCode
    PencilState.next (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
