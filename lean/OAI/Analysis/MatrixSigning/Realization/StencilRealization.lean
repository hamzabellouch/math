import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization
import OAI.Analysis.MatrixSigning.Realization.DependentRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*}

def vectorNeg : Realizes vectorCode vectorCode (List.map (fun q : ℚ => -q)) :=
  (identity ratCode).neg.map
lemma vectorNeg_ofFn {n : ℕ} (v : Fin n → ℚ) :
    (List.ofFn v).map (fun q => -q)=List.ofFn (-v) := by simp; rfl
lemma vectorScale_ofFn {n : ℕ} (t : ℚ) (v : Fin n → ℚ) :
    (List.ofFn v).map (fun q => t*q)=List.ofFn (t • v) := by simp;rfl

def stencilAt {ea : α → Word} (p : α → FaceParams) (pr : Realizes ea faceCode p)
    (v : (a : α) → Fin (p a).n → ℚ) (vr : Realizes ea vectorCode (fun a => List.ofFn (v a))) :
    Realizes ea ratCode (fun a => Difference.stencilValue
      (RationalFace.faceStencil (p a).coords (p a).base (p a).nu (p a).lam)
      (RationalFace.faceState (p a).base) (p a).schedule.h (v a)) :=
  let h : Realizes ea ratCode (fun a => (p a).schedule.h) := (pr.then fSchedule).then (parameterField 5)
  let y := ((pr.then fState).both ((h.both vr).then vectorScale)).then vectorAdd
  let point := (pr.both y).changeOutput facePointCode
    (fun a => ⟨p a,fun i => RationalFace.faceState (p a).base i+(p a).schedule.h*v a i⟩) (by
      intro a
      simp only [vectorScale_ofFn]
      change prodCode faceCode vectorCode (p a,zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0
        (List.ofFn (show Fin (p a).n → ℚ from RationalFace.faceState (p a).base),List.ofFn ((p a).schedule.h • v a)))=_
      rw [vectorAdd_ofFn]
      rfl)
  point.then faceStencil

abbrev FaceIndex := Σ p : FaceParams,Fin p.n
abbrev faceIndexCode := finFamilyCode faceCode FaceParams.n
def fiP : Realizes faceIndexCode faceCode (fun s : FaceIndex => s.1) := familyFirst
def fiI : Realizes faceIndexCode natCode (fun s : FaceIndex => s.2.val) := familyIndex
def fiBasis : Realizes faceIndexCode vectorCode
    (fun s : FaceIndex => List.ofFn (Difference.rationalBasis s.2)) :=
  (((fiP.then fN).both fiI).then basisVector).congr (fun s => basis_data s.2)

def stencilGradientEntry : Realizes faceIndexCode ratCode
    (fun s => Difference.stencilGradient (RationalFace.faceStencil s.1.coords s.1.base s.1.nu s.1.lam)
      (RationalFace.faceState s.1.base) s.1.schedule.h s.2) :=
  let plus := stencilAt (fun s : FaceIndex => s.1) fiP (fun s => Difference.rationalBasis s.2) fiBasis
  let minus := stencilAt (fun s : FaceIndex => s.1) fiP (fun s => -Difference.rationalBasis s.2)
    ((fiBasis.then vectorNeg).congr (fun _ => vectorNeg_ofFn _))
  (plus.sub minus).div ((constant faceIndexCode ratCode 2).mul ((fiP.then fSchedule).then (parameterField 5)))

def stencilGradient : Realizes faceCode vectorCode
    (fun p => List.ofFn (Difference.stencilGradient
      (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h)) :=
  stencilGradientEntry.tabulateFin fN

abbrev FaceDouble := Σ s : FaceIndex,Fin s.1.n
abbrev faceDoubleCode := finFamilyCode faceIndexCode (fun s : FaceIndex => s.1.n)
def fdS : Realizes faceDoubleCode faceIndexCode (fun s : FaceDouble => s.1) := familyFirst
def fdP := fdS.then fiP
def fdI := fdS.then fiI
def fdJ : Realizes faceDoubleCode natCode (fun s : FaceDouble => s.2.val) := familyIndex
def fdBasisI := fdS.then fiBasis
def fdBasisJ : Realizes faceDoubleCode vectorCode
    (fun s : FaceDouble => List.ofFn (Difference.rationalBasis s.2)) :=
  (((fdP.then fN).both fdJ).then basisVector).congr (fun s => basis_data s.2)

def stencilHessianEntry : Realizes faceDoubleCode ratCode
    (fun s => Difference.stencilHessian
      (RationalFace.faceStencil s.1.1.coords s.1.1.base s.1.1.nu s.1.1.lam)
      (RationalFace.faceState s.1.1.base) s.1.1.schedule.h s.1.2 s.2) :=
  let c (q : ℚ) := constant faceDoubleCode ratCode q
  let h : Realizes faceDoubleCode ratCode (fun s => s.1.1.schedule.h) := (fdP.then fSchedule).then (parameterField 5)
  let value := ((fdP.both (fdP.then fState)).changeOutput facePointCode
    (fun s => ⟨s.1.1,RationalFace.faceState s.1.1.base⟩) (fun _ => rfl)).then faceStencil
  let bi := fdBasisI
  let bj := fdBasisJ
  let nbi := (bi.then vectorNeg).congr (fun s => vectorNeg_ofFn _)
  let nbj := (bj.then vectorNeg).congr (fun s => vectorNeg_ofFn _)
  let query (v : (s : FaceDouble) → Fin s.1.1.n → ℚ)
      (vr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (v s))) :=
    stencilAt (fun s : FaceDouble => s.1.1) fdP v vr
  let plus := query (fun s => Difference.rationalBasis s.1.2) bi
  let minus := query (fun s => -Difference.rationalBasis s.1.2) nbi
  let add (v w : (s : FaceDouble) → Fin s.1.1.n → ℚ)
      (vr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (v s)))
      (wr : Realizes faceDoubleCode vectorCode (fun s => List.ofFn (w s))) :=
    (vr.both wr).then vectorAdd |>.congr (fun s => vectorAdd_ofFn _ _)
  let pp := query _ (add _ _ bi bj)
  let pm := query _ (add _ _ bi nbj)
  let mp := query _ (add _ _ nbi bj)
  let mm := query _ (add _ _ nbi nbj)
  let diag := ((plus.sub ((c 2).mul value)).add minus).div (h.pow 2)
  let off := (((pp.sub pm).sub mp).add mm).div ((c 4).mul (h.pow 2))
  (((fdI.both fdJ).then natEq).ite diag off).congr (by
    intro s
    simp only [Difference.stencilHessian,decide_eq_true_eq,sub_eq_add_neg]
    by_cases hij : s.1.2=s.2
    · simp only [hij,ite_true]
    · have hv : s.1.2.val≠s.2.val := fun hh => hij (Fin.ext hh)
      simp only [hij,hv,ite_false])

def stencilHessianRow := stencilHessianEntry.tabulateFin (fiP.then fN)
def stencilHessian : Realizes faceCode matrixCode
    (fun p => matrixData (Difference.stencilHessian
      (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h)) :=
  stencilHessianRow.tabulateFin fN

end CurrentKS.Realization

end

end OAI
