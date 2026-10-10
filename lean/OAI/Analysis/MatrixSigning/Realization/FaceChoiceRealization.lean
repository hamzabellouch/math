import Mathlib
import OAI.Analysis.MatrixSigning.Realization.SelectionRealization
import OAI.Analysis.MatrixSigning.Realization.CurvatureRealization
import OAI.Analysis.MatrixSigning.Realization.EndpointRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev FaceActive := {p : FaceParams // p.n ≠ 0}
def activeFaceCode (p : FaceActive) : Word := faceCode p.val
def faP : Realizes activeFaceCode faceCode Subtype.val :=
  (identity faceCode).reindex activeFaceCode Subtype.val (fun _ => rfl)
def FaceParams.gradient (p : FaceParams) := Difference.stencilGradient
  (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h
def FaceParams.hessian (p : FaceParams) := Difference.stencilHessian
  (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h
def FaceParams.curvatureParams (p : FaceParams) : CurvatureParams :=
  ⟨p.n,p.hessian,p.schedule.a,p.schedule.M,p.schedule.s,p.schedule.ρ⟩
def faceCurvatureParams : Realizes faceCode curvatureCode FaceParams.curvatureParams :=
  let sp := fSchedule
  (fN.both (stencilHessian.both ((sp.then (parameterField 2)).both
    ((sp.then (parameterField 3)).both ((sp.then (parameterField 4)).both (sp.then (parameterField 6))))))).changeOutput
    curvatureCode FaceParams.curvatureParams (fun _ => rfl)
def FaceParams.curvature (p : FaceParams) :=
  RationalRoot.computedCurvature p.hessian p.schedule.a p.schedule.M p.schedule.s p.schedule.ρ
def faceCurvature : Realizes faceCode vectorCode (fun p => p.curvature.elim [] List.ofFn) :=
  faceCurvatureParams.then computedCurvature

def FaceActive.gradientPoint (p : FaceActive) : Fin p.val.n → ℚ :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceState p.val.base+p.val.schedule.s • Difference.rationalGradientDirection p.val.gradient

def faGradientPoint : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.gradientPoint) :=
  let x := faP.then fState
  let step := (faP.then fSchedule).then (parameterField 4)
  let g := (faP.then stencilGradient).then gradientDirection
  ((x.both ((step.both g).then vectorScale)).then vectorAdd).congr (by
    intro p
    let : NeZero p.val.n := ⟨p.property⟩
    change zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0
      (List.ofFn (RationalFace.faceState p.val.base),
        (gradientDirectionData (List.ofFn p.val.gradient)).map (fun q => p.val.schedule.s*q))=_
    rw [gradientDirection_data,vectorScale_ofFn,vectorAdd_ofFn]
    rfl)

def vectorSub := (ratOp .sub).zipWith 0 0
lemma vectorSub_data {n : ℕ} (x y : Fin n → ℚ) :
    zipDefault (fun p : ℚ×ℚ => p.1-p.2) 0 0 (List.ofFn x,List.ofFn y)=List.ofFn (x-y) :=
  zipDefault_ofFn _ _ _ _ _
def curvatureCandidatesData (p : List ℚ×List ℚ) : List (List ℚ) :=
  if p.2.length=0 then [] else
    [zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0 p,zipDefault (fun z : ℚ×ℚ => z.1-z.2) 0 0 p]
def curvatureCandidates : Realizes (prodCode vectorCode vectorCode) (listCode vectorCode) curvatureCandidatesData :=
  let empty := ((second vectorCode vectorCode).then (lengthList ratCode)).then natIsZero
  let pair := (vectorAdd.both (vectorSub.then (singleton vectorCode))).then (consList vectorCode)
  (empty.ite (constant (prodCode vectorCode vectorCode) (listCode vectorCode) []) pair).congr (by
    intro p;simp only [curvatureCandidatesData,decide_eq_true_eq];rfl)
lemma curvatureCandidates_data {n : ℕ} [NeZero n] (x : Fin n → ℚ) (q : Option (Fin n → ℚ)) :
    curvatureCandidatesData (List.ofFn x,q.elim [] List.ofFn)=
      ((match q with | none => [] | some q => [x+q,x-q]).map List.ofFn) := by
  cases q with
  | none => simp [curvatureCandidatesData]
  | some q => simp only [Option.elim_some,curvatureCandidatesData,List.length_ofFn,NeZero.ne,ite_false,
      vectorAdd_ofFn,vectorSub_data,List.map_cons,List.map_nil]

def FaceActive.candidates (p : FaceActive) : List (Fin p.val.n → ℚ) :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceCandidates p.val.coords p.val.base p.val.nu p.val.lam

def faCandidates : Realizes activeFaceCode (listCode vectorCode)
    (fun p => p.candidates.map List.ofFn) :=
  let endpoints := (faP.then fState).then endpointCandidates
  let curves := (((faP.then fState).both (faP.then faceCurvature)).then curvatureCandidates)
  let inside := (faGradientPoint.both curves).then (consList vectorCode)
  ((endpoints.both inside).then (appendList vectorCode)).congr (by
    intro p
    let : NeZero p.val.n := ⟨p.property⟩
    change endpointData (List.ofFn (RationalFace.faceState p.val.base))++
      (List.ofFn p.gradientPoint::curvatureCandidatesData
        (List.ofFn (RationalFace.faceState p.val.base),p.val.curvature.elim [] List.ofFn))=_
    rw [endpoint_data,curvatureCandidates_data]
    simp only [FaceActive.candidates,RationalFace.faceCandidates,Difference.allCandidates,
      Difference.interiorCandidates,List.map_append,List.map_cons,FaceActive.gradientPoint,
      FaceParams.gradient,FaceParams.hessian,FaceParams.curvature,FaceParams.schedule]
    rfl)

def FaceActive.choice (p : FaceActive) : Fin p.val.n → ℚ :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceChoice p.val.coords p.val.base p.val.nu p.val.lam

def faCandidatePoints : Realizes activeFaceCode (listCode facePointCode)
    (fun p => p.candidates.map (fun y => (⟨p.val,y⟩ : FacePoint))) :=
  (((faP.both faCandidates).then (identity (prodCode faceCode vectorCode)).mapCtx)).changeOutput
    (listCode facePointCode) (fun p => p.candidates.map (fun y => (⟨p.val,y⟩ : FacePoint))) (by
      intro p
      simp only [listCode,FramedMapRoutine.tape,List.flatMap_map,List.map_map,Function.comp_def,id_eq]
      rfl)

def faChoice : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.choice) :=
  let defaultPoint := ((faP.both (faP.then fState)).changeOutput facePointCode
    (fun p => ⟨p.val,RationalFace.faceState p.val.base⟩) (fun _ => rfl))
  let scored := fpY.both faceScore
  let init := defaultPoint.then scored
  let all := faCandidatePoints.then scored.map
  (((init.both all).then (selectScored vectorCode)).then (first vectorCode ratCode)).congr (by
    intro p
    have h := selectScored_data (RationalFace.faceScore p.val.coords p.val.base p.val.nu p.val.lam)
      List.ofFn p.candidates (RationalFace.faceState p.val.base)
    simpa only [List.map_map,Function.comp_def,FaceActive.choice,RationalFace.faceChoice,FaceActive.candidates] using congrArg Prod.fst h)

end CurrentKS.Realization

end

end OAI
