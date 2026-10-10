import Mathlib
import OAI.Analysis.MatrixSigning.Realization.VectorRealization
import OAI.Analysis.MatrixSigning.Potential.Parameters2

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def Realizes.min (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea ratCode (fun x => min (f x) (g x)) :=
  ((r.le s).ite r s).congr (by intro x;simp [min_def])
def Realizes.max (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea ratCode (fun x => max (f x) (g x)) :=
  ((r.le s).ite s r).congr (by intro x;simp [max_def])
def Realizes.inv (r : Realizes ea ratCode f) : Realizes ea ratCode (fun x => (f x)⁻¹) :=
  ((constant ea ratCode 1).div r).congr (by intro x;exact one_div _)
def Realizes.eq (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea boolCode (fun x => decide (f x = g x)) :=
  ((r.le s).ite (s.le r) (constant ea boolCode false)).congr (by
    intro x
    rcases lt_trichotomy (f x) (g x) with h|h|h
    · simp [h.le,not_le.mpr h,ne_of_lt h]
    · simp [h]
    · simp [not_le.mpr h,ne_of_gt h])

abbrev scheduleArgsCode := prodCode natCode (prodCode natCode (prodCode ratCode ratCode))
def saD := first natCode (prodCode natCode (prodCode ratCode ratCode))
def saRest := second natCode (prodCode natCode (prodCode ratCode ratCode))
def saN := saRest.then (first natCode (prodCode ratCode ratCode))
def saScalars := saRest.then (second natCode (prodCode ratCode ratCode))
def saNu := saScalars.then (first ratCode ratCode)
def saLam := saScalars.then (second ratCode ratCode)
def saEpsilon := saNu.div (saD.then natToRat)
def saSigma := (saLam.pow 2).div saNu

def movementBudget : Realizes (prodCode natCode ratCode) ratCode
    (fun p => Schedule.movementBudget p.1 p.2) :=
  let c (q : ℚ) := constant (prodCode natCode ratCode) ratCode q
  let n := (first natCode ratCode).then natToRat
  let eps := second natCode ratCode
  let J := (c 1).add ((((c 3).mul n).pow 2).div (eps.div (c 40000)))
  let E := ((c 2).mul (J.pow 2)).mul (((c 1).add ((c 3).mul n)).pow 2)
  (c 1).max ((((c 48).mul E).div (c 23)).max ((c 4).mul ((c 1).add ((c 9).mul (n.pow 2)))))

def saThreshold :=
  saLam.div ((constant scheduleArgsCode ratCode 512).mul
    (((saN.both saEpsilon).then movementBudget).pow 2))

def saCoarse : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.coarseBudgetQ p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let n := saN.then natToRat
  ((((((c 200).add d).add saEpsilon.abs).add (((c 200).div saEpsilon).mul d)).add ((c 200).mul d)).add
    (d.add n)).add ((((c 384).mul n).mul ((c 1).add ((c 800).div (saSigma.pow 3)))))

def saCurve2 : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.valueCurve2Q p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let J := ((c (10^18)).mul d).mul (((c 1).add saEpsilon.inv).pow 4)
  let D := (c 300).mul (saCoarse.pow 5)
  ((c 1).add (saEpsilon.abs.mul ((c 2).mul d))).mul ((J.mul D).mul (((c 1).add (J.mul D)).pow 2))

def saCurve3 : Realizes scheduleArgsCode ratCode
    (fun p => Schedule.valueCurve3Q p.1 p.2.1 (p.2.2.1/(p.1:ℚ)) (p.2.2.2^2/p.2.2.1)) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let d := (saD.then natToRat).add (c 1)
  let J := ((c (10^18)).mul d).mul (((c 1).add saEpsilon.inv).pow 4)
  let D := (c 300).mul (saCoarse.pow 5)
  let JD := J.mul D
  let plus := (c 1).add JD
  ((c 1).add (saEpsilon.abs.mul ((c 2).mul d))).mul
    (JD.mul ((plus.pow 3).add (((c 3).mul plus).mul (JD.mul (plus.pow 2)))))

def saBudget :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (((c 1).add saCurve2).add saCurve3).add
    ((saLam.abs.mul (saN.then natToRat)).mul ((c 1).add ((c 800).div (saSigma.pow 3))))
def saStep :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (saSigma.div (c 4)).min ((saThreshold.div ((c 4).mul saBudget)).min (c (1/4)))
def saStencil :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  (saSigma.div (c 8)).min ((c 1).min (saThreshold.div (((c 64).mul saBudget).mul (saN.then natToRat))))
def saMesh :=
  (saStep.mul saThreshold).div
    (((constant scheduleArgsCode ratCode 4096).mul saBudget).mul (saN.then natToRat))
def parametersData (p : Schedule.Parameters) := [p.ε,p.σ,p.a,p.M,p.s,p.h,p.ρ,p.stencilError,p.selectionError]
def parametersCode (p : Schedule.Parameters) : Word := vectorCode (parametersData p)

def parameters : Realizes scheduleArgsCode parametersCode
    (fun p => Schedule.parameters p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  let c (q : ℚ) := constant scheduleArgsCode ratCode q
  let stencilErr := (saThreshold.mul (saStencil.pow 2)).div ((c 128).mul (saN.then natToRat))
  let selectionErr := (saThreshold.mul (saStep.pow 2)).div (c 4)
  let push {f : ℕ×(ℕ×(ℚ×ℚ)) → ℚ} {g : ℕ×(ℕ×(ℚ×ℚ)) → List ℚ}
      (r : Realizes scheduleArgsCode ratCode f) (s : Realizes scheduleArgsCode vectorCode g) :=
    (r.both s).then (consList ratCode)
  (push saEpsilon (push saSigma (push saThreshold (push saBudget (push saStep
    (push saStencil (push saMesh (push stencilErr (selectionErr.then (singletonRat)))))))))).changeOutput
    parametersCode (fun p => Schedule.parameters p.1 p.2.1 p.2.2.1 p.2.2.2) (fun _ => rfl)
where
  singletonRat : Realizes ratCode vectorCode (fun q => [q]) :=
    ((identity ratCode).both (constant ratCode vectorCode [])).then (consList ratCode)

def parameterField (i : ℕ) : Realizes parametersCode ratCode (fun p => (parametersData p).getD i 0) :=
  let view := (identity vectorCode).reindex parametersCode parametersData (fun _ => rfl)
  ((constant parametersCode natCode i).both view).then (getD ratCode 0)

end CurrentKS.Realization

end

end OAI
