import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.RootTolerance
import OAI.Analysis.MatrixSigning.Realization.RootRealization
import OAI.Analysis.MatrixSigning.Realization.ValueQueryRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

structure PotentialParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  x : Fin N → ℚ
  nu : ℚ
  lam : ℚ
  error : ℚ
abbrev potentialScalarsCode := prodCode ratCode (prodCode ratCode ratCode)
abbrev potentialDataCode := prodCode natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def PotentialParams.data (p : PotentialParams) :=
  (p.d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))),
    (List.ofFn p.x,(p.nu,(p.lam,p.error)))))
def potentialCode (p : PotentialParams) : Word := potentialDataCode p.data
def potentialView : Realizes potentialCode potentialDataCode PotentialParams.data :=
  (identity potentialDataCode).reindex potentialCode PotentialParams.data (fun _ => rfl)
def ppD : Realizes potentialCode natCode PotentialParams.d :=
  potentialView.then (first natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode)))
def ppRest := potentialView.then (second natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode)))
def ppAtoms := ppRest.then (first (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def ppArgs := ppRest.then (second (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def ppX : Realizes potentialCode vectorCode (fun p => List.ofFn p.x) :=
  ppArgs.then (first vectorCode potentialScalarsCode)
def ppScalars : Realizes potentialCode potentialScalarsCode (fun p => (p.nu,(p.lam,p.error))) :=
  ppArgs.then (second vectorCode potentialScalarsCode)
def ppNu : Realizes potentialCode ratCode PotentialParams.nu :=
  ppScalars.then (first ratCode (prodCode ratCode ratCode))
def ppLam : Realizes potentialCode ratCode PotentialParams.lam :=
  ppScalars.then ((second ratCode (prodCode ratCode ratCode)).then (first ratCode ratCode))
def ppError : Realizes potentialCode ratCode PotentialParams.error :=
  ppScalars.then ((second ratCode (prodCode ratCode ratCode)).then (second ratCode ratCode))
def ppN : Realizes potentialCode natCode PotentialParams.N :=
  (ppX.then (lengthList ratCode)).congr (by intro p;exact List.length_ofFn)
def ppRootTolerance : Realizes potentialCode ratCode
    (fun p => RationalSDP.rootTolerance p.d p.N p.lam p.error) :=
  let c (q : ℚ) := constant potentialCode ratCode q
  ppError.div ((c 2).mul ((((c 38400).mul (ppD.then natToRat)).add (ppLam.mul (ppN.then natToRat))).add (c 1)))
def PotentialParams.theta (p : PotentialParams) : Fin p.N → ℚ :=
  fun i => Scalar.approxPsi (p.x i) (RationalSDP.rootTolerance p.d p.N p.lam p.error)
def ppTheta : Realizes potentialCode vectorCode (fun p => List.ofFn p.theta) :=
  let one := ((second ratCode ratCode).both (first ratCode ratCode)).then approxPsi
  ((ppRootTolerance.both ppX).then one.mapCtx).congr (by
    intro p
    simp only [List.map_ofFn,Function.comp_def]
    rfl)
def PotentialParams.query (p : PotentialParams) : ValueQueryParams :=
  ⟨p.d,p.N,p.coords,p.x,p.theta,p.nu,p.error/4⟩
def ppQuery : Realizes potentialCode valueQueryCode PotentialParams.query :=
  let v := ppD.both (ppAtoms.both (ppX.both (ppTheta.both (ppNu.div (ppD.then natToRat)))))
  (v.both (ppError.div (constant potentialCode ratCode 4))).changeOutput valueQueryCode
    PotentialParams.query (fun _ => rfl)
def potentialQuery : Realizes potentialCode ratCode
    (fun p => RationalSDP.potentialQuery p.coords p.x p.nu p.lam p.error) :=
  ((ppQuery.then valueQuery).add (ppLam.mul (ppTheta.then sumRationals))).congr (by
    intro p
    simp only [List.sum_ofFn]
    rfl)

end CurrentKS.Realization

end

end OAI
