import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.RationalAtoms
import OAI.Analysis.MatrixSigning.Realization.ValueObjectiveRealization
import OAI.Analysis.MatrixSigning.Realization.OptimizeRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure ValueQueryParams where
  d : ℕ
  N : ℕ
  coords : Fin N → Fin d×Fin d → ℚ
  x : Fin N → ℚ
  theta : Fin N → ℚ
  nu : ℚ
  delta : ℚ
abbrev valueQueryDataCode := prodCode valueDataCode ratCode

def ValueQueryParams.data (p : ValueQueryParams) :=
  (valueData p.coords p.x p.theta (p.nu/p.d),p.delta)
def valueQueryCode (p : ValueQueryParams) : Word := valueQueryDataCode p.data
def vqView : Realizes valueQueryCode valueQueryDataCode ValueQueryParams.data :=
  (identity valueQueryDataCode).reindex valueQueryCode ValueQueryParams.data (fun _ => rfl)
def vqData : Realizes valueQueryCode valueDataCode
    (fun p => valueData p.coords p.x p.theta (p.nu/p.d)) :=
  vqView.then (first valueDataCode ratCode)
def vqDelta : Realizes valueQueryCode ratCode ValueQueryParams.delta :=
  vqView.then (second valueDataCode ratCode)

def valueLipschitz : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueLipschitz p.1 p.2.2.2.2) :=
  let one := constant valueDataCode ratCode 1
  let two := constant valueDataCode ratCode 2
  let d := vdD.then natToRat
  let n := (vdD.then valueDimension).then natToRat
  (n.add one).mul (one.add ((two.mul vdEps).mul d))
def valueOuterRadius : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueOuterRadius p.1 p.2.2.2.2) :=
  let c (q : ℚ) := constant valueDataCode ratCode q
  let d := vdD.then natToRat
  let n := (vdD.then valueDimension).then natToRat
  (n.add (c 1)).mul ((c 100).add (((c 400).div vdEps).mul (d.add (c 1))))
def valueInnerRadius : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueInnerRadius p.1) :=
  let c (q : ℚ) := constant valueDataCode ratCode q
  (c 1).div ((c 4000).mul (((vdD.then natToRat).pow 2).add (c 1)))

def ValueQueryParams.opt (p : ValueQueryParams) : OptParams :=
  let ε := p.nu/p.d
  let L := RationalSDP.valueLipschitz p.d ε
  let R := RationalSDP.valueOuterRadius p.d ε
  let r := RationalSDP.valueInnerRadius p.d
  ⟨RationalSDP.valueDimension p.d,_,
    RationalSDP.valuePencil p.coords p.x p.theta ε,
    RationalSDP.valueObjectiveCoeffs p.d ε,p.delta,
    RationalSDP.nearRadius p.delta L R r,R,100⟩

def vqOpt : Realizes valueQueryCode optCode ValueQueryParams.opt :=
  let L := vqData.then valueLipschitz
  let R := vqData.then valueOuterRadius
  let r := vqData.then valueInnerRadius
  let near := (vqDelta.div (L.mul (((constant valueQueryCode ratCode 2).mul R).add r))).mul r
  let B := vqData.then valuePencil
  let f := vqData.then valueCoeffs
  (B.both (f.both (vqDelta.both (near.both (R.both (constant valueQueryCode ratCode 100)))))).changeOutput
    optCode ValueQueryParams.opt (by
      intro p
      simp only [valuePencil_data,valueCoeffs_data]
      rfl)

def vqFuel : Realizes valueQueryCode natCode (fun p => RationalSDP.optimizeFuel p.delta 100) :=
  let q := (constant valueQueryCode ratCode 200).div vqDelta
  (((q.then ratCeil).both (constant valueQueryCode natCode 3)).then natAdd).congr (by
    intro p
    simp only [RationalSDP.optimizeFuel]
    norm_num)

def valueQueryPoint : Realizes valueQueryCode vectorCode
    (fun p => List.ofFn (RationalSDP.valueQueryPoint p.coords p.x p.theta p.nu p.delta)) :=
  (vqOpt.both vqFuel).then optimize

def valueQuery : Realizes valueQueryCode ratCode
    (fun p => RationalSDP.valueQuery p.coords p.x p.theta p.nu p.delta) :=
  ((vqData.both valueQueryPoint).then valueObjective).congr (by
    intro p
    exact valueObjective_data p.coords p.x p.theta (p.nu/p.d) _)

end CurrentKS.Realization

end

end OAI
