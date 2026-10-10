import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactRationalPlaceProgram
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! A source-edge record contains the original integer endpoints and the
nineteen calibrated lengths. The whole local coordinate list is computed
by the same orientation and height routines used in the geometric proof. -/

noncomputable section
namespace ContinuumCoulomb.ContactPlacedGadgetProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ((ℤ × ℤ) × (ℤ × ℤ)) × ContactRationalGadget.Input

def inputCode : Input → List Bool :=
  prodCode ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode

def placement (x : Input) : ContactGridEdge := canonicalContactEdge x.1.1 x.1.2

def position (x : Input) (s : ContactGadgetSite) : ℚ × ℚ :=
  ContactRationalGlobal.rationalPlace (placement x) (ContactRationalGadget.position x.2 s)

noncomputable opaque placementProgram : Procedure inputCode ContactCanonicalEdgeProgram.edgeCode
    placement := ContactCanonicalEdgeProgram.program.comp
      (Procedure.first ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode)

noncomputable opaque gadgetProgram : Procedure inputCode ContactRationalGadget.inputCode Prod.snd :=
  Procedure.second ContactCanonicalEdgeProgram.inputCode ContactRationalGadget.inputCode

noncomputable opaque positionProgram (s : ContactGadgetSite) :
    Procedure inputCode ContactRationalGadget.pointCode (fun x => position x s) :=
  ContactRationalPlaceProgram.program.comp
    (placementProgram.pair ((ContactRationalGadget.positionProgram s).comp gadgetProgram))

noncomputable def pointListProgram : (ss : List ContactGadgetSite) →
    Procedure inputCode (listCode ContactRationalGadget.pointCode)
      (fun x => ss.map (position x))
  | [] => (Procedure.constant inputCode (listCode ContactRationalGadget.pointCode) []).congrFun
      (by intro x; rfl)
  | s :: ss => ((Procedure.listCons ContactRationalGadget.pointCode).comp
      ((positionProgram s).pair (pointListProgram ss))).congrFun (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode ContactRationalGadget.pointCode)
      (fun x => ContactRationalGadget.sites.map (position x)) :=
  (pointListProgram ContactRationalGadget.sites).toTM2

end ContinuumCoulomb.ContactPlacedGadgetProgram

end

end OAI
