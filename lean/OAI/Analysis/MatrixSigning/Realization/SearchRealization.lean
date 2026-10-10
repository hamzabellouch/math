import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SearchStep
import OAI.Analysis.MatrixSigning.Realization.RoundedStepRealization
import OAI.Analysis.MatrixSigning.Realization.RatFieldsRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure SearchState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  r : ℚ
  R : ℚ
  y : Fin n → ℚ

def searchStateData (s : SearchState) : PencilData×(StepParameters×List ℚ) :=
  (pencilData s.B,((s.r,s.R),List.ofFn s.y))
def searchStateCode (s : SearchState) : Word := pencilStateDataCode (searchStateData s)
def searchView : Realizes searchStateCode pencilStateDataCode searchStateData :=
  (identity pencilStateDataCode).reindex searchStateCode searchStateData (fun _ => rfl)
def searchPencil : Realizes searchStateCode pencilCode (fun s => pencilData s.B) :=
  searchView.then (first pencilCode (prodCode stepParametersCode vectorCode))
def searchParameters : Realizes searchStateCode stepParametersCode (fun s => (s.r,s.R)) :=
  searchView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (first stepParametersCode vectorCode))
def searchY : Realizes searchStateCode vectorCode (fun s => List.ofFn s.y) :=
  searchView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (second stepParametersCode vectorCode))
def searchDim : Realizes searchStateCode natCode SearchState.n :=
  (searchY.then (lengthList ratCode)).congr (fun _ => List.length_ofFn)
def searchStepRealizes : Realizes searchStateCode ratCode
    (fun s => RationalSDP.searchStep s.n s.r) :=
  (searchParameters.then (first ratCode ratCode)).div
    ((searchDim.then natToRat).add (constant searchStateCode ratCode 1))
def searchMeshRealizes : Realizes searchStateCode ratCode
    (fun s => RationalSDP.searchMesh s.n s.r s.R) :=
  let dim1 := (searchDim.then natToRat).add (constant searchStateCode ratCode 1)
  let S := searchStepRealizes
  let R := searchParameters.then (second ratCode ratCode)
  (S.pow 2).div (((constant searchStateCode ratCode 16).mul dim1).mul
    ((R.add S).add (constant searchStateCode ratCode 1)))
def searchFuelRealizes : Realizes searchStateCode natCode
    (fun s => RationalSDP.searchFuel s.n s.r s.R) :=
  let R := searchParameters.then (second ratCode ratCode)
  ((((constant searchStateCode ratCode 4).mul (R.pow 2)).div
    (searchStepRealizes.pow 2)).then ratCeil).then natSucc

def SearchState.init (s : SearchState) : PencilState :=
  ⟨s.n,s.m,s.B,RationalSDP.searchStep s.n s.r,RationalSDP.searchMesh s.n s.r s.R,s.y⟩
def searchInit : Realizes searchStateCode pencilStateCode SearchState.init :=
  (searchPencil.both ((searchStepRealizes.both searchMeshRealizes).both searchY)).changeOutput
    pencilStateCode SearchState.init (fun _ => rfl)

lemma pencilNext_iterate (s : PencilState) (k : ℕ) :
    PencilState.next^[k] s={s with y := (s.B.next s.step s.mesh)^[k] s.y} := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply'];rfl

def search : Realizes searchStateCode vectorCode
    (fun s => List.ofFn (s.B.search s.r s.R s.y)) :=
  (((searchFuelRealizes.both searchInit).then pencilNext.iterate).then stateY).congr (by
    intro s
    exact congrArg (fun t : PencilState => List.ofFn t.y)
      (pencilNext_iterate s.init (RationalSDP.searchFuel s.n s.r s.R)))

end CurrentKS.Realization

end

end OAI
