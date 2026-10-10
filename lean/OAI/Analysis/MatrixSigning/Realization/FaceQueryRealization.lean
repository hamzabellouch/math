import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.FaceStencil
import OAI.Analysis.MatrixSigning.Realization.ScheduleRealization
import OAI.Analysis.MatrixSigning.Realization.FaceArrayRealization
import OAI.Analysis.MatrixSigning.Realization.PotentialRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure FaceParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  base : Fin N → ℚ
  nu : ℚ
  lam : ℚ
abbrev faceDataCode := prodCode natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def FaceParams.data (p : FaceParams) :=
  (p.d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))),
    (List.ofFn p.base,(p.nu,p.lam))))
def faceCode (p : FaceParams) : Word := faceDataCode p.data
def faceView : Realizes faceCode faceDataCode FaceParams.data :=
  (identity faceDataCode).reindex faceCode FaceParams.data (fun _ => rfl)
def fD := faceView.then (first natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode))))
def fRest := faceView.then (second natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode))))
def fAtoms := fRest.then (first (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def fArgs := fRest.then (second (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def fBase : Realizes faceCode vectorCode (fun p => List.ofFn p.base) :=
  fArgs.then (first vectorCode (prodCode ratCode ratCode))
def fScalars := fArgs.then (second vectorCode (prodCode ratCode ratCode))
def fNu := fScalars.then (first ratCode ratCode)
def fLam := fScalars.then (second ratCode ratCode)
def fIndices : Realizes faceCode indicesCode
    (fun p => List.ofFn (fun j => (RationalFace.activeIndex p.base j).val)) :=
  (fBase.then activeIndices).congr (fun p => activeIndex_data p.base)
abbrev FaceParams.n (p : FaceParams) : ℕ := (RationalFace.activeIndices p.base).length
def fN : Realizes faceCode natCode FaceParams.n :=
  (fIndices.then (lengthList natCode)).congr (fun _ => List.length_ofFn)
def FaceParams.schedule (p : FaceParams) : Schedule.Parameters := Schedule.parameters p.d p.n p.nu p.lam
def fSchedule : Realizes faceCode parametersCode FaceParams.schedule :=
  (fD.both (fN.both fScalars)).then parameters

def gatherData (p : List ℚ×List ℕ) : List ℚ := p.2.map (fun i => p.1.getD i 0)
def gather : Realizes (prodCode vectorCode indicesCode) vectorCode gatherData :=
  (((second vectorCode natCode).both (first vectorCode natCode)).then (getD ratCode 0)).mapCtx
lemma gather_data {N n : ℕ} (x : Fin N → ℚ) (e : Fin n → Fin N) :
    gatherData (List.ofFn x,List.ofFn (fun j => (e j).val))=List.ofFn (fun j => x (e j)) := by
  simp only [gatherData,List.map_ofFn,Function.comp_def,getD_ofFn]
def fState : Realizes faceCode vectorCode (fun p => List.ofFn (RationalFace.faceState p.base)) :=
  ((fBase.both fIndices).then gather).congr (fun p => gather_data p.base (RationalFace.activeIndex p.base))

structure FacePoint where
  p : FaceParams
  y : Fin p.n → ℚ
def facePointData (s : FacePoint) := (s.p,List.ofFn s.y)
def facePointCode (s : FacePoint) : Word := prodCode faceCode vectorCode (facePointData s)
def facePointView : Realizes facePointCode (prodCode faceCode vectorCode) facePointData :=
  (identity (prodCode faceCode vectorCode)).reindex facePointCode facePointData (fun _ => rfl)
def fpP : Realizes facePointCode faceCode FacePoint.p := facePointView.then (first faceCode vectorCode)
def fpY : Realizes facePointCode vectorCode (fun s => List.ofFn s.y) := facePointView.then (second faceCode vectorCode)
def fpExtend : Realizes facePointCode vectorCode
    (fun s => List.ofFn (RationalFace.extend (RationalFace.activeIndex s.p.base) s.p.base s.y)) :=
  (((fpP.then fIndices).both ((fpP.then fBase).both fpY)).then extendVector).congr
    (fun s => extendData_data (RationalFace.activeIndex s.p.base) s.p.base s.y)
def FacePoint.potential (q : FacePoint×ℚ) : PotentialParams :=
  ⟨q.1.p.d,q.1.p.N,q.1.p.coords,
    RationalFace.extend (RationalFace.activeIndex q.1.p.base) q.1.p.base q.1.y,
    q.1.p.nu,q.1.p.lam,q.2⟩
def fpPotential : Realizes (prodCode facePointCode ratCode) potentialCode FacePoint.potential :=
  let s := first facePointCode ratCode
  let p := s.then fpP
  let err := second facePointCode ratCode
  ((p.then fD).both ((p.then fAtoms).both ((s.then fpExtend).both
    ((p.then fNu).both ((p.then fLam).both err))))).changeOutput potentialCode
    FacePoint.potential (fun _ => rfl)
def faceQuery : Realizes (prodCode facePointCode ratCode) ratCode
    (fun q => RationalSDP.faceQuery q.1.p.coords q.1.p.base q.1.y q.1.p.nu q.1.p.lam q.2) :=
  fpPotential.then potentialQuery

def faceStencil : Realizes facePointCode ratCode
    (fun q => RationalFace.faceStencil q.p.coords q.p.base q.p.nu q.p.lam q.y) :=
  let err := (fpP.then fSchedule).then (parameterField 7)
  ((identity facePointCode).both err).then faceQuery

def faceScore : Realizes facePointCode ratCode
    (fun q => RationalFace.faceScore q.p.coords q.p.base q.p.nu q.p.lam q.y) :=
  let err := (fpP.then fSchedule).then (parameterField 8)
  ((identity facePointCode).both err).then faceQuery

end CurrentKS.Realization

end

end OAI
