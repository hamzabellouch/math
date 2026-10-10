import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactCanonicalEdgeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactRationalGadgetProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalGlobal

namespace OAI

/-! Exact strip placement uses only rational arithmetic and the two
computed orientation bits. It preserves the original lattice endpoints. -/

namespace ContinuumCoulomb.ContactRationalPlaceProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ContactGridEdge × (ℚ × ℚ)

def inputCode : Input → List Bool :=
  prodCode ContactCanonicalEdgeProgram.edgeCode ContactRationalGadget.pointCode

noncomputable opaque edgeProgram : Procedure inputCode ContactCanonicalEdgeProgram.edgeCode
    Prod.fst := Procedure.first _ _

noncomputable opaque pointProgram : Procedure inputCode ContactRationalGadget.pointCode
    Prod.snd := Procedure.second _ _

noncomputable opaque verticalProgram : Procedure inputCode Procedure.boolCode
    (fun x => x.1.vertical) :=
  ((Procedure.first Procedure.boolCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)).precompose
      (fun e : ContactGridEdge => (e.vertical, (e.anchor, e.reversed)))).comp edgeProgram

noncomputable opaque edgeTailProgram : Procedure inputCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)
    (fun x => (x.1.anchor, x.1.reversed)) :=
  ((Procedure.second Procedure.boolCode
    (prodCode ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode)).precompose
      (fun e : ContactGridEdge => (e.vertical, (e.anchor, e.reversed)))).comp edgeProgram

noncomputable opaque reverseProgram : Procedure inputCode Procedure.boolCode
    (fun x => x.1.reversed) :=
  (Procedure.second ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode).comp edgeTailProgram

noncomputable opaque anchorProgram : Procedure inputCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => x.1.anchor) :=
  (Procedure.first ContactCanonicalEdgeProgram.latticeCode Procedure.boolCode).comp edgeTailProgram

noncomputable opaque anchorXProgram : Procedure inputCode ratCode
    (fun x => (x.1.anchor.1 : ℚ)) :=
  Procedure.intToRat.comp ((Procedure.first intCode intCode).comp anchorProgram)

noncomputable opaque anchorYProgram : Procedure inputCode ratCode
    (fun x => (x.1.anchor.2 : ℚ)) :=
  Procedure.intToRat.comp ((Procedure.second intCode intCode).comp anchorProgram)

noncomputable opaque rawXProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode ratCode).comp pointProgram

noncomputable opaque rawYProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second ratCode ratCode).comp pointProgram

noncomputable opaque reflectedXProgram : Procedure inputCode ratCode
    (fun x => if x.1.reversed then 17 - x.2.1 else x.2.1) :=
  Procedure.conditional reverseProgram
    (Procedure.ratSub.comp ((Procedure.constant inputCode ratCode 17).pair rawXProgram)) rawXProgram

noncomputable opaque baseXProgram : Procedure inputCode ratCode
    (fun x => 17 * (x.1.anchor.1 : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 17).pair anchorXProgram)

noncomputable opaque baseYProgram : Procedure inputCode ratCode
    (fun x => 17 * (x.1.anchor.2 : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 17).pair anchorYProgram)

noncomputable opaque xProgram : Procedure inputCode ratCode
    (fun x => if x.1.vertical then 17 * (x.1.anchor.1 : ℚ) - x.2.2
      else 17 * (x.1.anchor.1 : ℚ) + (if x.1.reversed then 17 - x.2.1 else x.2.1)) :=
  Procedure.conditional verticalProgram
    (Procedure.ratSub.comp (baseXProgram.pair rawYProgram))
    (Procedure.ratAdd.comp (baseXProgram.pair reflectedXProgram))

noncomputable opaque yProgram : Procedure inputCode ratCode
    (fun x => if x.1.vertical then 17 * (x.1.anchor.2 : ℚ) +
      (if x.1.reversed then 17 - x.2.1 else x.2.1)
      else 17 * (x.1.anchor.2 : ℚ) + x.2.2) :=
  Procedure.conditional verticalProgram
    (Procedure.ratAdd.comp (baseYProgram.pair reflectedXProgram))
    (Procedure.ratAdd.comp (baseYProgram.pair rawYProgram))

noncomputable opaque program : Procedure inputCode ContactRationalGadget.pointCode
    (fun x => ContactRationalGlobal.rationalPlace x.1 x.2) :=
  (xProgram.pair yProgram).congrFun (by
    intro x
    cases hv : x.1.vertical <;> cases hr : x.1.reversed <;>
      simp [ContactRationalGlobal.rationalPlace, hv, hr])

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    ContactRationalGadget.pointCode (fun x => ContactRationalGlobal.rationalPlace x.1 x.2) :=
  program.toTM2

end ContinuumCoulomb.ContactRationalPlaceProgram

end OAI
