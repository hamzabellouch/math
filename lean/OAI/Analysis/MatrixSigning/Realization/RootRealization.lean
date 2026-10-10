import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SquareInterval
import OAI.Analysis.MatrixSigning.Arithmetic.CubeInterval
import OAI.Analysis.MatrixSigning.Realization.RatFieldsRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev rootStateCode := prodCode ratCode (prodCode ratCode ratCode)
def rootStep (pow : ℕ) (p : ℚ×(ℚ×ℚ)) : ℚ×(ℚ×ℚ) :=
  let mid := (p.2.1+p.2.2)/2
  (p.1,if mid^pow≤p.1 then (mid,p.2.2) else (p.2.1,mid))
def rootStepRealizes (pow : ℕ) : Realizes rootStateCode rootStateCode (rootStep pow) :=
  let q := first ratCode (prodCode ratCode ratCode)
  let s := second ratCode (prodCode ratCode ratCode)
  let lo := s.then (first ratCode ratCode)
  let hi := s.then (second ratCode ratCode)
  let mid := (lo.add hi).div (constant rootStateCode ratCode 2)
  (q.both (((mid.pow pow).le q).ite (mid.both hi) (lo.both mid))).congr (by
    intro p;simp [rootStep])

lemma square_iterate (q : ℚ) (k : ℕ) :
    (rootStep 2)^[k] (q,(0,1))=(q,RationalRoot.squareInterval q k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl
lemma cube_iterate (q : ℚ) (k : ℕ) :
    (rootStep 3)^[k] (q,(0,1))=(q,Scalar.cubeInterval q k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl

def rootRun (pow : ℕ) : Realizes (prodCode ratCode natCode)
    (prodCode ratCode ratCode) (fun p => ((rootStep pow)^[p.2] (p.1,(0,1))).2) :=
  let q := first ratCode natCode
  let fuel := second ratCode natCode
  let init := q.both (constant (prodCode ratCode natCode) (prodCode ratCode ratCode) (0,1))
  ((fuel.both init).then (rootStepRealizes pow).iterate).then
    (second ratCode (prodCode ratCode ratCode))

def upperSqrt : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => RationalRoot.upperSqrt p.1 p.2) :=
  let q := first ratCode ratCode
  let fuel := (second ratCode ratCode).then ratDenSize
  (((q.both fuel).then (rootRun 2)).then (second ratCode ratCode)).congr (by
    intro p
    simp only [square_iterate,RationalRoot.upperSqrt])

def approxPsi : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => Scalar.approxPsi p.1 p.2) :=
  let x := first ratCode ratCode
  let fuel := (second ratCode ratCode).then ratDenSize
  let q := (constant (prodCode ratCode ratCode) ratCode 1).sub (x.pow 2)
  (((q.both fuel).then (rootRun 3)).then (first ratCode ratCode)).congr (by
    intro p
    simp only [cube_iterate,Scalar.approxPsi])

end CurrentKS.Realization

end

end OAI
