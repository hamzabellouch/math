import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Transition
import OAI.Analysis.MatrixSigning.Realization.FaceChoiceRealization
import OAI.Analysis.MatrixSigning.Realization.DependentBranchRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a))) :
    Realizes ea faceCode (fun a => {f a with base := g a}) :=
  ((p.then fD).both ((p.then fAtoms).both (y.both (p.then fScalars)))).changeOutput
    faceCode (fun a => {f a with base := g a}) (fun _ => rfl)

def FaceActive.nextBase (p : FaceActive) : Fin p.val.N → ℚ :=
  RationalFace.freezeAll (p.val.lam^2/p.val.nu)
    (RationalFace.extend (RationalFace.activeIndex p.val.base) p.val.base p.choice)
def faNextBase : Realizes activeFaceCode vectorCode (fun p => List.ofFn p.nextBase) :=
  let point := (faP.both faChoice).changeOutput facePointCode (fun p => ⟨p.val,p.choice⟩) (fun _ => rfl)
  let sigma := ((faP.then fLam).pow 2).div (faP.then fNu)
  ((sigma.both (point.then fpExtend)).then freezeVector).congr (fun _ => freezeVector_data _ _)

def FaceParams.next (p : FaceParams) : FaceParams :=
  {p with base := (RationalFace.transition p.coords p.nu p.lam p.base).getD p.base}

def faceNext : Realizes faceCode faceCode FaceParams.next :=
  let test := (fN.then natIsZero).congr (fun _ => rfl)
  let stop := (identity faceCode).reindex (fun p : {p : FaceParams // p.n=0} => faceCode p.val) Subtype.val (fun _ => rfl)
  let advance := packFace faP faNextBase
  (test.dite stop advance).congr (by
    intro p
    by_cases hn : p.n=0
    · simp only [hn,dite_eq_left,FaceParams.next,RationalFace.transition, id_eq,Option.getD_none]
    · simp only [hn,FaceParams.next,RationalFace.transition]
      rfl)

lemma minList_reverse (xs : List ℚ) : xs.reverse.foldl min 1=Descent.minList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,Descent.minList]
    exact min_comm _ _
def minList : Realizes vectorCode ratCode Descent.minList :=
  let one := constant vectorCode ratCode 1
  let op := (first ratCode ratCode).min (second ratCode ratCode)
  ((one.both (reverseList ratCode)).then op.fold).congr minList_reverse

def fUniformDrop : Realizes faceCode ratCode
    (fun p => RationalFace.uniformDrop p.d p.N p.nu p.lam) :=
  let p := first faceCode natCode
  let n := second faceCode natCode
  let args := (p.then fD).both (n.both (p.then fScalars))
  let schedule := args.then parameters
  let drop := (schedule.then (parameterField 2)).mul ((schedule.then (parameterField 4)).pow 2)
  let count := ((fBase.then (lengthList ratCode)).then natSucc)
  ((((identity faceCode).both count).then drop.tabulate).then minList).congr (by
    intro p
    simp only [List.length_ofFn,id_eq]
    rfl)
def fFuel : Realizes faceCode natCode
    (fun p => Descent.fuel (RationalFace.uniformDrop p.d p.N p.nu p.lam)) :=
  (((constant faceCode ratCode 100).div fUniformDrop).then ratCeil).then natSucc

def FaceParams.start (p : FaceParams) : FaceParams :=
  {p with base := RationalFace.freezeAll (p.lam^2/p.nu) 0}
def faceStart : Realizes faceCode faceCode FaceParams.start :=
  let zeros := ((constant faceCode ratCode 0).both (fBase.then (lengthList ratCode))).then (replicateList ratCode)
  let sigma := (fLam.pow 2).div fNu
  let frozen := ((sigma.both zeros).then freezeVector).congr (by
    intro p
    rw [List.length_ofFn,← List.ofFn_const]
    exact freezeVector_data _ _)
  packFace (identity faceCode) frozen

lemma run_eq_iterate {α : Type*} (step : α → Option α) (k : ℕ) (x : α) :
    Descent.run step k x=(fun a => (step a).getD a)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Descent.run,Function.iterate_succ_apply]
    cases he : step x with
    | none =>
      simp only [Option.getD_none]
      exact (Function.iterate_fixed (by simp [he]) k).symm
    | some y => simpa only [Option.getD_some] using ih y

lemma next_pack (d N : ℕ) (coords : Fin N → Fin d×Fin d → ℚ) (nu lam : ℚ) (x : Fin N → ℚ) :
    FaceParams.next ⟨d,N,coords,x,nu,lam⟩=
      ⟨d,N,coords,(RationalFace.transition coords nu lam x).getD x,nu,lam⟩ := rfl
lemma next_iterate (p : FaceParams) (k : ℕ) :
    FaceParams.next^[k] p={p with base := Descent.run (RationalFace.transition p.coords p.nu p.lam) k p.base} := by
  rcases p with ⟨d,N,coords,x,nu,lam⟩
  rw [run_eq_iterate]
  let g (x : Fin N → ℚ) : FaceParams := ⟨d,N,coords,x,nu,lam⟩
  have h : Function.Semiconj g (fun x => (RationalFace.transition coords nu lam x).getD x) FaceParams.next :=
    fun x => rfl
  exact (h.iterate_right k x).symm

def faceRun : Realizes faceCode vectorCode
    (fun p => List.ofFn (RationalFace.rationalRun p.coords p.nu p.lam)) :=
  (((fFuel.both faceStart).then faceNext.iterate).then fBase).congr (by
    intro p
    rw [next_iterate]
    rfl)

end CurrentKS.Realization

end

end OAI
