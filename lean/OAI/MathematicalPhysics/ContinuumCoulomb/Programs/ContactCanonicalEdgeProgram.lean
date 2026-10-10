import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCanonicalEdge
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactHeightProgram

namespace OAI

/-! The canonical lattice strip is computed by integer comparisons. -/

namespace ContinuumCoulomb.ContactCanonicalEdgeProgram
open ExactQuantumFactoring.BitStackProgram

def latticeCode : (ℤ × ℤ) → List Bool := prodCode intCode intCode
def inputCode : ((ℤ × ℤ) × (ℤ × ℤ)) → List Bool := prodCode latticeCode latticeCode
def edgeCode (e : ContactGridEdge) : List Bool :=
  prodCode Procedure.boolCode (prodCode latticeCode Procedure.boolCode)
    (e.vertical, (e.anchor, e.reversed))

noncomputable opaque integerEqual : Procedure (prodCode intCode intCode)
    Procedure.boolCode (fun x => decide (x.1 = x.2)) :=
  (Procedure.binaryZero.comp (Procedure.intAbs.comp Procedure.intSub)).congrFun (by
    intro x
    simp only [Function.comp_apply, Int.natAbs_eq_zero, sub_eq_zero])

noncomputable opaque integerLess : Procedure (prodCode intCode intCode)
    Procedure.boolCode (fun x => decide (x.1 < x.2)) :=
  (Procedure.intSign.comp Procedure.intSub).congrFun (by
    intro x
    simp only [Function.comp_apply, sub_neg])

noncomputable opaque leftProgram : Procedure inputCode latticeCode Prod.fst :=
  Procedure.first latticeCode latticeCode
noncomputable opaque rightProgram : Procedure inputCode latticeCode Prod.snd :=
  Procedure.second latticeCode latticeCode
noncomputable opaque leftXProgram : Procedure inputCode intCode (fun x => x.1.1) :=
  (Procedure.first intCode intCode).comp leftProgram
noncomputable opaque leftYProgram : Procedure inputCode intCode (fun x => x.1.2) :=
  (Procedure.second intCode intCode).comp leftProgram
noncomputable opaque rightXProgram : Procedure inputCode intCode (fun x => x.2.1) :=
  (Procedure.first intCode intCode).comp rightProgram
noncomputable opaque rightYProgram : Procedure inputCode intCode (fun x => x.2.2) :=
  (Procedure.second intCode intCode).comp rightProgram

noncomputable opaque verticalProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.1.1 = x.2.1)) := integerEqual.comp (leftXProgram.pair rightXProgram)

noncomputable opaque forwardProgram : Procedure inputCode Procedure.boolCode
    (fun x => if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2) else decide (x.1.1 < x.2.1)) :=
  Procedure.conditional verticalProgram (integerLess.comp (leftYProgram.pair rightYProgram))
    (integerLess.comp (leftXProgram.pair rightXProgram))

noncomputable opaque anchorProgram : Procedure inputCode latticeCode
    (fun x => if (if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2)
      else decide (x.1.1 < x.2.1)) then x.1 else x.2) :=
  Procedure.conditional forwardProgram leftProgram rightProgram

noncomputable opaque reverseProgram : Procedure inputCode Procedure.boolCode
    (fun x => !(if decide (x.1.1 = x.2.1) then decide (x.1.2 < x.2.2)
      else decide (x.1.1 < x.2.1))) := Procedure.boolNot.comp forwardProgram

noncomputable opaque program : Procedure inputCode edgeCode
    (fun x => canonicalContactEdge x.1 x.2) :=
  (verticalProgram.pair (anchorProgram.pair reverseProgram)).result (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode edgeCode
    (fun x => canonicalContactEdge x.1 x.2) := program.toTM2

end ContinuumCoulomb.ContactCanonicalEdgeProgram

end OAI
