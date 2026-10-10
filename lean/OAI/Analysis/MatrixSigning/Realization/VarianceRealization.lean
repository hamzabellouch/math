import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.NormalizedRun
import OAI.Analysis.MatrixSigning.Realization.FaceRunRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

structure MatrixGrid where
  n : ℕ
  M : Matrix (Fin n) (Fin n) ℚ
  den : ℕ
abbrev matrixGridDataCode := prodCode natCode (prodCode matrixCode natCode)
def MatrixGrid.data (p : MatrixGrid) := (p.n,(matrixData p.M,p.den))
def matrixGridCode (p : MatrixGrid) : Word := matrixGridDataCode p.data
def mgView : Realizes matrixGridCode matrixGridDataCode MatrixGrid.data :=
  (identity matrixGridDataCode).reindex matrixGridCode MatrixGrid.data (fun _ => rfl)
def mgN := mgView.then (first natCode (prodCode matrixCode natCode))
def mgRest := mgView.then (second natCode (prodCode matrixCode natCode))
def mgM := mgRest.then (first matrixCode natCode)
def mgDen := mgRest.then (second matrixCode natCode)
def MatrixGrid.test (p : MatrixGrid) (q : ℚ) : Bool :=
  (KS.W17.rationalNegativeWitness p.n (q • 1-p.M)).isNone

def mgShift : Realizes (prodCode matrixGridCode ratCode) matrixObjectCode
    (fun p => ⟨p.1.n,p.2 • 1-p.1.M⟩) :=
  let p := first matrixGridCode ratCode
  let q := second matrixGridCode ratCode
  let M := ((q.both ((p.then mgN).then identityMatrix)).then matrixScale).both (p.then mgM) |>.then matrixSub
  ((p.then mgN).both M).changeOutput matrixObjectCode (fun p => ⟨p.1.n,p.2 • 1-p.1.M⟩) (by
    intro p
    simp only [identityMatrix_data,matrixScale_data]
    change prodCode natCode matrixCode (p.1.n,
      matrixSubData (matrixData (p.2 • (1 : Matrix (Fin p.1.n) (Fin p.1.n) ℚ)),matrixData p.1.M))=_
    rw [matrixSub_data]
    rfl)
def mgTest : Realizes (prodCode matrixGridCode ratCode) boolCode (fun p => p.1.test p.2) :=
  (mgShift.then isPSD).congr (by
    intro p
    unfold MatrixGrid.test
    cases KS.W17.rationalNegativeWitness p.1.n (p.2 • 1-p.1.M) <;> rfl)

abbrev gridStateCode := prodCode matrixGridCode (prodCode natCode natCode)
def gridStepData (s : MatrixGrid×(ℕ×ℕ)) :=
  (s.1,(s.2.1+1,if s.1.test ((s.2.1:ℚ)/s.1.den) then s.2.2 else s.2.1+1))
def gridStep : Realizes gridStateCode gridStateCode gridStepData :=
  let p := first matrixGridCode (prodCode natCode natCode)
  let args := second matrixGridCode (prodCode natCode natCode)
  let k := args.then (first natCode natCode)
  let prev := args.then (second natCode natCode)
  let q := (k.then natToRat).div ((p.then mgDen).then natToRat)
  let test := (p.both q).then mgTest
  p.both ((k.then natSucc).both (test.ite prev (k.then natSucc)))
lemma grid_iterate (p : MatrixGrid) (k : ℕ) :
    gridStepData^[k] (p,(0,0))=(p,(k,RationalGrid.upperIndex p.den p.test k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

def gridUpper : Realizes matrixGridCode ratCode (fun p => RationalGrid.upper p.den p.test) :=
  let init := (identity matrixGridCode).both (constant matrixGridCode (prodCode natCode natCode) (0,0))
  let run := ((mgDen.both init).then gridStep.iterate)
  let result := run.then ((second matrixGridCode (prodCode natCode natCode)).then (second natCode natCode))
  ((result.then natToRat).div (mgDen.then natToRat)).congr (by
    intro p
    rw [grid_iterate]
    rfl)

lemma foldAdd_matrixData {n : ℕ} (xs : List (Matrix (Fin n) (Fin n) ℚ))
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (xs.map matrixData).foldl
      (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
      (matrixData A)=matrixData (A+xs.sum) := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,matrixAdd_data,ih,List.sum_cons,add_assoc]
lemma matrix_fold_sum {n m : ℕ} (f : Fin n → Matrix (Fin m) (Fin m) ℚ) :
    (List.ofFn (fun i => matrixData (f i))).foldl
      (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
      (matrixData (0 : Matrix (Fin m) (Fin m) ℚ))=matrixData (∑ i,f i) := by
  have h := foldAdd_matrixData (List.ofFn f) 0
  simpa only [List.map_ofFn,Function.comp_def,List.sum_ofFn,zero_add] using h

def fVariance : Realizes faceCode matrixCode
    (fun p => matrixData (RationalSDP.rationalVariance p.coords)) :=
  let squares := fAtoms.then ((identity matrixCode).both (identity matrixCode) |>.then matrixMul).map
  let zero := ((fD.both fD).then natAdd).then zeroMatrix
  ((zero.both squares).then matrixAdd.fold).congr (by
    intro p
    change ((List.ofFn fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))).map
      (fun M => matrixMulData (M,M))).foldl
        (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
        (matrixData (0 : Matrix (Fin (p.d+p.d)) (Fin (p.d+p.d)) ℚ))=_
    simp only [List.map_ofFn,Function.comp_def,matrixMul_data]
    rw [matrix_fold_sum]
    rfl)

def fVarianceGrid : Realizes faceCode matrixGridCode
    (fun p => ⟨p.d+p.d,RationalSDP.rationalVariance p.coords,1000*p.N*p.d^2⟩) :=
  let den := ((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
    ((fD.then natToRat).pow 2)).then ratCeil
  (((fD.both fD).then natAdd).both (fVariance.both den)).changeOutput matrixGridCode
    (fun p => ⟨p.d+p.d,RationalSDP.rationalVariance p.coords,1000*p.N*p.d^2⟩) (by
      intro p
      simp only [List.length_ofFn,FaceParams.data]
      have h : ⌈(p.N:ℚ)*1000*(p.d:ℚ)^2⌉₊=1000*p.N*p.d^2 := by
        have he : (p.N:ℚ)*1000*(p.d:ℚ)^2=((1000*p.N*p.d^2:ℕ):ℚ) := by push_cast;ring
        rw [he,Nat.ceil_natCast]
      rw [h]
      rfl)
def varianceQuery : Realizes faceCode ratCode (fun p => RationalSDP.varianceQuery p.coords) :=
  fVarianceGrid.then gridUpper

def faceNormalized : Realizes faceCode faceCode
    (fun p => {p with nu := RationalSDP.varianceQuery p.coords, lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}) :=
  let nu := varianceQuery
  let root := (nu.both nu).then upperSqrt
  let lam := root.div ((constant faceCode ratCode 200).mul ((fBase.then (lengthList ratCode)).then natToRat))
  (fD.both (fAtoms.both (fBase.both (nu.both lam)))).changeOutput faceCode
    (fun p => {p with nu := RationalSDP.varianceQuery p.coords, lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}) (by
      intro p;simp only [List.length_ofFn];rfl)
def normalizedRun : Realizes faceCode vectorCode
    (fun p => List.ofFn (RationalFace.normalizedRun p.coords)) :=
  faceNormalized.then faceRun

end CurrentKS.Realization

end

end OAI
