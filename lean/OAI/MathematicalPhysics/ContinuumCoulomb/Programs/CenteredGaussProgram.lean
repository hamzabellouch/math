import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGaussLabels
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGaussList

namespace OAI

/-! Literal polynomial generation of the complete rectangular Gauss-label
list. The three integer radii are unary, so the cubic number of output cells
is polynomial in the encoded input size. -/

namespace ContinuumCoulomb.CenteredGaussLabels
open ExactQuantumFactoring.BitStackProgram

private theorem flatten_code_bound {α : Type} (ea : α → List Bool) (xs : List (List α)) :
    (listCode ea xs.flatten).length ≤ (listCode (listCode ea) xs).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    have h := listCode_length_append ea x xs.flatten
    simp only [List.flatten_cons,listCode_length_cons]
    omega

private theorem fold_append {α : Type} (xs : List (List α)) (ys : List α) :
    xs.foldl (fun ys x => ys++x) ys = ys++xs.flatten := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.flatten_cons,List.append_assoc]

private noncomputable def flattenProgram {α : Type} (ea : α → List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten := by
  let step := (Procedure.listAppend ea d).comp (Procedure.swap (listCode ea) (listCode ea))
  let p := Procedure.foldList [] step Polynomial.X (by
    intro xs ys i
    change (listCode ea ((xs.take i).foldl (fun ys x => ys++x) ys)).length ≤ _
    rw [fold_append]
    have h := listCode_length_append ea ys (xs.take i).flatten
    have hf := flatten_code_bound ea (xs.take i)
    have ht := listCode_length_take_le (listCode ea) i xs
    simp only [Polynomial.eval_X]
    omega)
  exact (p.comp ((Procedure.identity (listCode (listCode ea))).pair
    (Procedure.constant (listCode (listCode ea)) (listCode ea) []))).congrFun (by
      intro xs
      change xs.foldl (fun ys x => ys++x) [] = xs.flatten
      simpa only [List.nil_append] using fold_append xs [])

private noncomputable def productProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a : α) (b : β) : Procedure (prodCode (listCode ea) (listCode eb))
      (listCode (prodCode ea eb)) (fun x => x.1 ×ˢ x.2) := by
  let row := (Procedure.listMapWith (ea := ea) (eb := eb) (ec := prodCode ea eb)
    (f := fun a b => (a,b)) b (a,b) (Procedure.identity (prodCode ea eb))).comp
      (Procedure.swap (listCode eb) ea)
  let rows := (Procedure.listMapWith (ea := listCode eb) (eb := ea)
    (ec := listCode (prodCode ea eb)) (f := fun ys a => ys.map (fun b => (a,b))) a [] row).comp
      (Procedure.swap (listCode ea) (listCode eb))
  exact ((flattenProgram (prodCode ea eb) (a,b)).comp rows).congrFun (by intro x; rfl)

def radiiCode : Radii → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

private noncomputable opaque integerStep : Procedure (prodCode unaryCode unaryCode) intCode
    (fun x => (x.1:ℤ)-(x.2:ℤ)) := by
  let cast := Procedure.natToInt.comp Procedure.unaryToBits
  exact Procedure.intSub.comp
    ((cast.comp (Procedure.first unaryCode unaryCode)).pair
      (cast.comp (Procedure.second unaryCode unaryCode)))

noncomputable opaque integersProgram : Procedure unaryCode (listCode intCode) integers := by
  let count := Procedure.unarySuccessor.comp (Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode 2).pair (Procedure.identity unaryCode)))
  exact ((Procedure.tabulate (ea := unaryCode) (eb := intCode)
    (f := fun R i => (i:ℤ)-(R:ℤ)) 0 integerStep).comp
      (count.pair (Procedure.identity unaryCode))).congrFun (by intro R; rfl)

private noncomputable opaque firstRadiusProgram : Procedure radiiCode unaryCode Prod.fst :=
  Procedure.first _ _
private noncomputable opaque tailRadiiProgram : Procedure radiiCode (prodCode unaryCode unaryCode) Prod.snd :=
  Procedure.second _ _
private noncomputable opaque secondRadiusProgram : Procedure radiiCode unaryCode (fun r => r.2.1) :=
  (Procedure.first _ _).comp tailRadiiProgram
private noncomputable opaque thirdRadiusProgram : Procedure radiiCode unaryCode (fun r => r.2.2) :=
  (Procedure.second _ _).comp tailRadiiProgram

noncomputable opaque cellsProgram : Procedure radiiCode (listCode EulerRegisters.registersCode) cells := by
  let yz := (productProgram intCode intCode (0:ℤ) (0:ℤ)).comp
    ((integersProgram.comp secondRadiusProgram).pair (integersProgram.comp thirdRadiusProgram))
  exact (productProgram intCode (prodCode intCode intCode) (0:ℤ) (0,0)).comp
    ((integersProgram.comp firstRadiusProgram).pair yz)

noncomputable opaque labelsProgram : Procedure radiiCode (listCode TransformedGauss.labelCode) labels :=
  (productProgram EulerRegisters.registersCode RationalGaussNodes.signsCode (0,(0,0))
    (false,(false,false))).comp
      (cellsProgram.pair (Procedure.constant radiiCode (listCode RationalGaussNodes.signsCode) signs))

noncomputable def labelsCertificate : Turing.TM2ComputableInPolyTime radiiCode
    (listCode TransformedGauss.labelCode) labels := labelsProgram.toTM2

end ContinuumCoulomb.CenteredGaussLabels

end OAI
