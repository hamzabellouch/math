import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.ValueObjectiveCoeffs
import OAI.Analysis.MatrixSigning.Realization.ValueEvalRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def traceData (M : MatrixData) : ℚ :=
  ((List.range M.length).map (fun i => (M.getD i []).getD i 0)).sum

def traceMatrix : Realizes matrixCode ratCode traceData :=
  let M := first matrixCode natCode
  let i := second matrixCode natCode
  let entry := (M.both (i.both i)).then matrixEntry
  ((((identity matrixCode).both (lengthList vectorCode)).then entry.tabulate).then sumRationals)

lemma trace_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : traceData (matrixData A)=Matrix.trace A := by
  unfold traceData matrixData
  simp only [List.length_ofFn,range_map_fin]
  have h : (fun i : Fin n => ((List.ofFn fun i => List.ofFn (A i)).getD i.val []).getD i.val 0)=
      fun i => A i i := by
    funext i
    rw [getD_ofFn,getD_ofFn]
  rw [h,List.sum_ofFn]
  rfl

def valueObjectiveData (p : ValueEvalData) : ℚ :=
  p.2.getD 0 0 + p.1.2.2.2.2*(traceData (coordinateData false (p.1.1,p.2))+
    traceData (coordinateData true (p.1.1,p.2)))
def valueObjective : Realizes valueEvalCode ratCode valueObjectiveData :=
  let dy := veD.both veY
  let t0 := (dy.then (coordinates false)).then traceMatrix
  let t1 := (dy.then (coordinates true)).then traceMatrix
  veTime.add (veEps.mul (t0.add t1))
lemma valueObjective_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    valueObjectiveData (valueData coords x θ ε,List.ofFn y)=RationalSDP.valueObjective d ε y := by
  unfold valueObjectiveData
  change (List.ofFn y).getD 0 0+ε*(traceData (coordinateData false (d,List.ofFn y))+
    traceData (coordinateData true (d,List.ofFn y)))=_
  erw [time_getD,coordinates_data,coordinates_data,trace_data,trace_data,RationalSDP.valueObjective_apply]
  simp only [Matrix.trace,Matrix.diag,Finset.sum_add_distrib]

def valueCoeffsData (p : ValueData) : List ℚ :=
  (List.range (RationalSDP.valueDimension p.1)).map
    (fun i => valueObjectiveData (p,basisData (RationalSDP.valueDimension p.1,i)))
def valueCoeffs : Realizes valueDataCode vectorCode valueCoeffsData :=
  let p := first valueDataCode natCode
  let n := (p.then vdD).then valueDimension
  let i := second valueDataCode natCode
  let basis := (n.both i).then basisVector
  let one := (p.both basis).then valueObjective
  ((identity valueDataCode).both (vdD.then valueDimension)).then one.tabulate
lemma valueCoeffs_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    valueCoeffsData (valueData coords x θ ε)=List.ofFn (RationalSDP.valueObjectiveCoeffs d ε) := by
  unfold valueCoeffsData
  change (List.range (RationalSDP.valueDimension d)).map _=_
  rw [range_map_fin]
  apply congrArg List.ofFn
  funext i
  erw [basis_data]
  exact (valueObjective_data coords x θ ε (Pi.single i (1:ℚ))).trans (by
    simpa using (RationalSDP.valueObjectiveCoeffs_dot ε (Pi.single i (1:ℚ))).symm)

def valuePencilData (p : ValueData) : PencilData :=
  pencilFromEvalData valueEvalData (p,RationalSDP.valueDimension p.1)
def valuePencil : Realizes valueDataCode pencilCode valuePencilData :=
  ((identity valueDataCode).both (vdD.then valueDimension)).then valueEval.pencilFromEval
lemma valuePencil_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    valuePencilData (valueData coords x θ ε)=pencilData (RationalSDP.valuePencil coords x θ ε) :=
  pencilFromEval_data _ _ _ (valueEval_data coords x θ ε)

end CurrentKS.Realization

end OAI
