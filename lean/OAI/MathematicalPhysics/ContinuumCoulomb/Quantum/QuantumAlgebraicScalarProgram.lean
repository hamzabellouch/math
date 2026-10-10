import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalar
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram

namespace OAI

/-! Literal polynomial programs for the exact algebraic history scalars.
Each operation uses only rational arithmetic on four registers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicScalar
open ExactQuantumFactoring.BitStackProgram

def realCode : RealScalar → List Bool := prodCode ratCode ratCode
def scalarCode : Scalar → List Bool := prodCode realCode realCode

noncomputable opaque realRatProgram : Procedure ratCode realCode realRat :=
  (Procedure.identity ratCode).pair (Procedure.constant ratCode ratCode 0)

noncomputable opaque realAddProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realAdd x.1 x.2) := by
  let l := Procedure.first realCode realCode
  let r := Procedure.second realCode realCode
  let a := (Procedure.first ratCode ratCode).comp l
  let b := (Procedure.second ratCode ratCode).comp l
  let c := (Procedure.first ratCode ratCode).comp r
  let d := (Procedure.second ratCode ratCode).comp r
  exact (Procedure.ratAdd.comp (a.pair c)).pair (Procedure.ratAdd.comp (b.pair d))

noncomputable opaque realNegProgram : Procedure realCode realCode realNeg :=
  (Procedure.ratNeg.comp (Procedure.first ratCode ratCode)).pair
    (Procedure.ratNeg.comp (Procedure.second ratCode ratCode))

noncomputable opaque realSubProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realSub x.1 x.2) :=
  realAddProgram.comp ((Procedure.first realCode realCode).pair
    (realNegProgram.comp (Procedure.second realCode realCode)))

noncomputable opaque realMulProgram : Procedure (prodCode realCode realCode) realCode
    (fun x => realMul x.1 x.2) := by
  let l := Procedure.first realCode realCode
  let r := Procedure.second realCode realCode
  let a := (Procedure.first ratCode ratCode).comp l
  let b := (Procedure.second ratCode ratCode).comp l
  let c := (Procedure.first ratCode ratCode).comp r
  let d := (Procedure.second ratCode ratCode).comp r
  let ac := Procedure.ratMul.comp (a.pair c)
  let bd := Procedure.ratMul.comp (b.pair d)
  let ad := Procedure.ratMul.comp (a.pair d)
  let bc := Procedure.ratMul.comp (b.pair c)
  let half := Procedure.ratDiv.comp
    (bd.pair (Procedure.constant (prodCode realCode realCode) ratCode 2))
  exact (Procedure.ratAdd.comp (ac.pair half)).pair (Procedure.ratAdd.comp (ad.pair bc))

noncomputable opaque ratProgram : Procedure ratCode scalarCode rat :=
  realRatProgram.pair (Procedure.constant ratCode realCode (realRat 0))

noncomputable opaque addProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => add x.1 x.2) := by
  let l := Procedure.first scalarCode scalarCode
  let r := Procedure.second scalarCode scalarCode
  let re := Procedure.first realCode realCode
  let im := Procedure.second realCode realCode
  exact (realAddProgram.comp ((re.comp l).pair (re.comp r))).pair
    (realAddProgram.comp ((im.comp l).pair (im.comp r)))

noncomputable opaque negProgram : Procedure scalarCode scalarCode neg :=
  (realNegProgram.comp (Procedure.first realCode realCode)).pair
    (realNegProgram.comp (Procedure.second realCode realCode))

noncomputable opaque subProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => sub x.1 x.2) :=
  addProgram.comp ((Procedure.first scalarCode scalarCode).pair
    (negProgram.comp (Procedure.second scalarCode scalarCode)))

noncomputable opaque mulProgram : Procedure (prodCode scalarCode scalarCode) scalarCode
    (fun x => mul x.1 x.2) := by
  let l := Procedure.first scalarCode scalarCode
  let r := Procedure.second scalarCode scalarCode
  let re := Procedure.first realCode realCode
  let im := Procedure.second realCode realCode
  let ac := realMulProgram.comp ((re.comp l).pair (re.comp r))
  let bd := realMulProgram.comp ((im.comp l).pair (im.comp r))
  let ad := realMulProgram.comp ((re.comp l).pair (im.comp r))
  let bc := realMulProgram.comp ((im.comp l).pair (re.comp r))
  exact (realSubProgram.comp (ac.pair bd)).pair (realAddProgram.comp (ad.pair bc))

noncomputable opaque conjProgram : Procedure scalarCode scalarCode conj :=
  (Procedure.first realCode realCode).pair
    (realNegProgram.comp (Procedure.second realCode realCode))

noncomputable opaque realPartProgram : Procedure scalarCode scalarCode realPart :=
  (Procedure.first realCode realCode).pair (Procedure.constant scalarCode realCode (realRat 0))

noncomputable opaque imagPartProgram : Procedure scalarCode scalarCode imagPart :=
  (Procedure.second realCode realCode).pair (Procedure.constant scalarCode realCode (realRat 0))

/-- Finite sums used by a fixed local matrix are bounded-depth compositions. -/
noncomputable def fixedSumProgram {α : Type} (ea : α → List Bool) (m : ℕ)
    (f : Fin m → α → Scalar) (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => sum (List.ofFn (fun i => f i x))) := by
  induction m with
  | zero => exact (Procedure.constant ea scalarCode (rat 0)).congrFun (by intro x; rfl)
  | succ m ih =>
    exact (addProgram.comp ((p 0).pair
      (ih (fun i => f i.succ) (fun i => p i.succ)))).congrFun (by
        intro x
        simp only [List.ofFn_succ,sum,Function.comp_apply])

noncomputable def fixedProductProgram {α : Type} (ea : α → List Bool) (m : ℕ)
    (f : Fin m → α → Scalar) (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => product (List.ofFn (fun i => f i x))) := by
  induction m with
  | zero => exact (Procedure.constant ea scalarCode (rat 1)).congrFun (by intro x; rfl)
  | succ m ih =>
    exact (mulProgram.comp ((p 0).pair
      (ih (fun i => f i.succ) (fun i => p i.succ)))).congrFun (by
        intro x
        simp only [List.ofFn_succ,product,Function.comp_apply])

def sampleCode : (ℕ × RealScalar) → List Bool := prodCode unaryCode realCode

noncomputable opaque sampleProgram : Procedure sampleCode ratCode (fun x => sample x.1 x.2) := by
  let k := Procedure.first unaryCode realCode
  let x := Procedure.second unaryCode realCode
  let a := (Procedure.first ratCode ratCode).comp x
  let b := (Procedure.second ratCode ratCode).comp x
  let root := RationalSquareRoot.program.comp
    (k.pair (Procedure.constant sampleCode ratCode (1/2)))
  exact Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (b.pair root)))

noncomputable def sampleCertificate : Turing.TM2ComputableInPolyTime sampleCode ratCode
    (fun x => sample x.1 x.2) := sampleProgram.toTM2

end ContinuumCoulomb.QuantumAlgebraicScalar

end

end OAI
