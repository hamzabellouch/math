import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Level
import OAI.Analysis.MatrixSigning.Realization.SearchRealization
import OAI.Analysis.MatrixSigning.Realization.LevelPencilRealization
import OAI.Analysis.MatrixSigning.Realization.WitnessRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure OptParams where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  f : Fin n → ℚ
  delta : ℚ
  r : ℚ
  R : ℚ
  U : ℚ
abbrev optScalarsCode := prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))
abbrev optDataCode := prodCode pencilCode (prodCode vectorCode optScalarsCode)
def optData (p : OptParams) := (pencilData p.B,(List.ofFn p.f,(p.delta,(p.r,(p.R,p.U)))))
def optCode (p : OptParams) : Word := optDataCode (optData p)
def optView : Realizes optCode optDataCode optData :=
  (identity optDataCode).reindex optCode optData (fun _ => rfl)
def optB : Realizes optCode pencilCode (fun p => pencilData p.B) :=
  optView.then (first pencilCode (prodCode vectorCode optScalarsCode))
def optF : Realizes optCode vectorCode (fun p => List.ofFn p.f) :=
  optView.then ((second pencilCode (prodCode vectorCode optScalarsCode)).then
    (first vectorCode optScalarsCode))
def optScalars : Realizes optCode optScalarsCode (fun p => (p.delta,(p.r,(p.R,p.U)))) :=
  optView.then ((second pencilCode (prodCode vectorCode optScalarsCode)).then
    (second vectorCode optScalarsCode))
def optDelta : Realizes optCode ratCode OptParams.delta :=
  optScalars.then (first ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def optRest : Realizes optCode (prodCode ratCode (prodCode ratCode ratCode)) (fun p => (p.r,(p.R,p.U))) :=
  optScalars.then (second ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def optRadius : Realizes optCode stepParametersCode (fun p => (p.r,p.R)) :=
  (optRest.then (first ratCode (prodCode ratCode ratCode))).both
    (optRest.then ((second ratCode (prodCode ratCode ratCode)).then (first ratCode ratCode)))
def optUpper : Realizes optCode ratCode OptParams.U :=
  optRest.then ((second ratCode (prodCode ratCode ratCode)).then (second ratCode ratCode))

def optLevel : Realizes (prodCode optCode natCode) ratCode
    (fun p => RationalSDP.level p.1.delta p.1.U p.2) :=
  let p := first optCode natCode
  let k := (second optCode natCode).then natToRat
  (p.then optUpper).neg.add (k.mul (p.then optDelta))
def optLevelPencil : Realizes (prodCode optCode natCode) pencilCode
    (fun p => pencilData (p.1.B.withLevel p.1.f (RationalSDP.level p.1.delta p.1.U p.2))) :=
  let p := first optCode natCode
  (((p.then optB).both ((p.then optF).both optLevel)).then withLevel).congr
    (fun p => withLevel_data p.1.B p.1.f _)

def candidateSearch (p : OptParams×ℕ) : SearchState :=
  ⟨p.1.n,p.1.m+1,p.1.B.withLevel p.1.f (RationalSDP.level p.1.delta p.1.U p.2),p.1.r,p.1.R,0⟩
def optCandidate : Realizes (prodCode optCode natCode) vectorCode
    (fun p => List.ofFn (p.1.B.levelCandidate p.1.f p.1.delta p.1.r p.1.R p.1.U p.2)) :=
  let p := first optCode natCode
  let zero := ((constant (prodCode optCode natCode) ratCode 0).both
    ((p.then optF).then (lengthList ratCode))).then (replicateList ratCode)
  let prep := (optLevelPencil.both ((p.then optRadius).both zero)).changeOutput
    searchStateCode candidateSearch (by
      intro p
      simp only [List.length_ofFn,searchStateCode,searchStateData,candidateSearch,
        pencilStateDataCode,Pi.zero_def,List.ofFn_const])
  prep.then search

structure OptState where
  p : OptParams
  k : ℕ
  y : Fin p.n → ℚ

def optStateData (s : OptState) := (s.p,(s.k,List.ofFn s.y))
abbrev optStateDataCode := prodCode optCode (prodCode natCode vectorCode)
def optStateCode (s : OptState) : Word := optStateDataCode (optStateData s)
def optStateView : Realizes optStateCode optStateDataCode optStateData :=
  (identity optStateDataCode).reindex optStateCode optStateData (fun _ => rfl)
def osP : Realizes optStateCode optCode OptState.p :=
  optStateView.then (first optCode (prodCode natCode vectorCode))
def osK : Realizes optStateCode natCode OptState.k :=
  optStateView.then ((second optCode (prodCode natCode vectorCode)).then (first natCode vectorCode))
def osY : Realizes optStateCode vectorCode (fun s => List.ofFn s.y) :=
  optStateView.then ((second optCode (prodCode natCode vectorCode)).then (second natCode vectorCode))
def OptState.feasibility (s : OptState) : WitnessState :=
  ⟨s.p.n,s.p.m+1,s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k),s.y⟩
def osFeasible : Realizes optStateCode boolCode
    (fun s => decide ((s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k)).witness s.y=none)) :=
  ((((osP.both osK).then optLevelPencil).both osY).changeOutput witnessStateCode
    OptState.feasibility (fun _ => rfl)).then witnessNone

def OptState.next (s : OptState) : OptState :=
  ⟨s.p,s.k+1,if (s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k)).witness s.y=none
    then s.y else s.p.B.levelCandidate s.p.f s.p.delta s.p.r s.p.R s.p.U (s.k+1)⟩
def osNext : Realizes optStateCode optStateCode OptState.next :=
  let nextY := osFeasible.ite osY ((osP.both (osK.then natSucc)).then optCandidate)
  (osP.both ((osK.then natSucc).both nextY)).changeOutput optStateCode OptState.next (by
    intro s
    unfold optStateCode optStateData OptState.next
    split_ifs <;> simp_all [optStateDataCode])

def OptParams.init (p : OptParams) : OptState :=
  ⟨p,0,p.B.levelCandidate p.f p.delta p.r p.R p.U 0⟩
def optInit : Realizes optCode optStateCode OptParams.init :=
  let cand := ((identity optCode).both (constant optCode natCode 0)).then optCandidate
  ((identity optCode).both ((constant optCode natCode 0).both cand)).changeOutput optStateCode
    OptParams.init (fun _ => rfl)

lemma opt_iterate (p : OptParams) (k : ℕ) :
    OptState.next^[k] p.init=⟨p,k,p.B.optimize p.f p.delta p.r p.R p.U k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl

def optimize : Realizes (prodCode optCode natCode) vectorCode
    (fun p => List.ofFn (p.1.B.optimize p.1.f p.1.delta p.1.r p.1.R p.1.U p.2)) :=
  let init := (first optCode natCode).then optInit
  let k := second optCode natCode
  (((k.both init).then osNext.iterate).then osY).congr (by
    intro p
    exact congrArg (fun s : OptState => List.ofFn s.y) (opt_iterate p.1 p.2))

end CurrentKS.Realization

end

end OAI
