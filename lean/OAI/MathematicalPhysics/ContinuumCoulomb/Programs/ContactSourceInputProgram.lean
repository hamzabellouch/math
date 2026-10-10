import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactLocalInputProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactGeometryBlockProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorListProgram

namespace OAI

/-! A literal polynomial-time program turns the source coordinate/bond
lists and calibrated final-edge lengths into all rational contact sites. -/

noncomputable section
namespace ContinuumCoulomb.ContactSourceInputProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (List (ℤ × ℤ) × (List MediatorListProgram.Bond × List ℚ))

def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)))

abbrev LoopInput := ℕ × Input

def loopCode : LoopInput → List Bool := prodCode unaryCode inputCode

def bond (x : LoopInput) : MediatorListProgram.Bond :=
  (x.2.2.2.1.drop x.1).headD MediatorListProgram.zeroBond

def edge (x : LoopInput) : ContactPlacedGadgetProgram.Input :=
  (((x.2.2.1.drop (bond x).1).headD (0, 0),
      (x.2.2.1.drop (bond x).2.1).headD (0, 0)),
    ContactLocalInputProgram.record (x.2.1, (x.2.2.2.1.length,
      (x.1, (decide ((bond x).2.2 < 0), x.2.2.2.2)))))

def edges (x : Input) : List ContactPlacedGadgetProgram.Input :=
  (List.range x.2.2.1.length).map (fun i => edge (i, x))

def positions (x : Input) : List (ℚ × ℚ) :=
  ContactGeometryBlockProgram.positions (x.2.1, edges x)

noncomputable opaque indexProgram : Procedure loopCode unaryCode Prod.fst :=
  Procedure.first unaryCode inputCode

noncomputable opaque inputProgram : Procedure loopCode inputCode Prod.snd :=
  Procedure.second unaryCode inputCode

noncomputable opaque precisionProgram : Procedure loopCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode _).comp inputProgram

noncomputable opaque dataProgram : Procedure loopCode
    (prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
      (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second unaryCode _).comp inputProgram

noncomputable opaque coordinatesProgram : Procedure loopCode
    (listCode ContactCanonicalEdgeProgram.latticeCode) (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp dataProgram

noncomputable opaque listsProgram : Procedure loopCode
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram

noncomputable opaque bondsProgram : Procedure loopCode
    (listCode MediatorListProgram.bondCode) (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp listsProgram

noncomputable opaque lengthsProgram : Procedure loopCode (listCode ratCode) (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp listsProgram

noncomputable opaque countProgram : Procedure loopCode unaryCode (fun x => x.2.2.2.1.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp bondsProgram

noncomputable opaque bondProgram : Procedure loopCode MediatorListProgram.bondCode bond :=
  (Procedure.listGet MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp
    ((Procedure.unaryToBits.comp indexProgram).pair bondsProgram)

noncomputable opaque leftIndexProgram : Procedure loopCode Nat.bits (fun x => (bond x).1) :=
  (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp bondProgram

noncomputable opaque bondTailProgram : Procedure loopCode (prodCode Nat.bits ratCode)
    (fun x => (bond x).2) := (Procedure.second Nat.bits _).comp bondProgram

noncomputable opaque rightIndexProgram : Procedure loopCode Nat.bits (fun x => (bond x).2.1) :=
  (Procedure.first Nat.bits ratCode).comp bondTailProgram

noncomputable opaque weightProgram : Procedure loopCode ratCode (fun x => (bond x).2.2) :=
  (Procedure.second Nat.bits ratCode).comp bondTailProgram

noncomputable opaque signProgram : Procedure loopCode Procedure.boolCode
    (fun x => decide ((bond x).2.2 < 0)) :=
  (Procedure.intSign.comp (Procedure.ratNum.comp weightProgram)).congrFun (by
    intro x
    simp only [Function.comp_apply, Rat.num_neg])

noncomputable opaque leftProgram : Procedure loopCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => (x.2.2.1.drop (bond x).1).headD (0, 0)) :=
  (Procedure.listGet ContactCanonicalEdgeProgram.latticeCode (0, 0)).comp
    (leftIndexProgram.pair coordinatesProgram)

noncomputable opaque rightProgram : Procedure loopCode ContactCanonicalEdgeProgram.latticeCode
    (fun x => (x.2.2.1.drop (bond x).2.1).headD (0, 0)) :=
  (Procedure.listGet ContactCanonicalEdgeProgram.latticeCode (0, 0)).comp
    (rightIndexProgram.pair coordinatesProgram)

noncomputable opaque localProgram : Procedure loopCode ContactRationalGadget.inputCode
    (fun x => ContactLocalInputProgram.record (x.2.1, (x.2.2.2.1.length,
      (x.1, (decide ((bond x).2.2 < 0), x.2.2.2.2))))) :=
  ContactLocalInputProgram.program.comp (precisionProgram.pair
    (countProgram.pair (indexProgram.pair (signProgram.pair lengthsProgram))))

noncomputable opaque edgeProgram : Procedure loopCode ContactPlacedGadgetProgram.inputCode edge :=
  (leftProgram.pair rightProgram).pair localProgram

noncomputable opaque edgesProgram : Procedure inputCode
    (listCode ContactPlacedGadgetProgram.inputCode) edges := by
  let lists : Procedure inputCode
      (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))
      (fun x => x.2.2) := (Procedure.second _ _).comp (Procedure.second unaryCode _)
  let bonds := (Procedure.first (listCode MediatorListProgram.bondCode) (listCode ratCode)).comp lists
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    MediatorListProgram.bondCode MediatorListProgram.zeroBond).comp bonds
  exact ((Procedure.tabulate (ea := inputCode) (eb := ContactPlacedGadgetProgram.inputCode)
    (f := fun x i => edge (i, x)) ContactGeometryBlockProgram.defaultEdge edgeProgram).comp
      (count.pair (Procedure.identity inputCode))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode
    (listCode ContactRationalGadget.pointCode) positions :=
  ContactGeometryBlockProgram.program.comp
    (((Procedure.first _ _).comp (Procedure.second unaryCode _)).pair edgesProgram)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode ContactRationalGadget.pointCode) positions := program.toTM2

def scaledInputCode : (ℚ × Input) → List Bool := prodCode ratCode inputCode

def scalePoint (x : ℚ × (ℚ × ℚ)) : ℚ × ℚ := (x.1 * x.2.1, x.1 * x.2.2)

noncomputable opaque scalePointProgram : Procedure
    (prodCode ratCode ContactRationalGadget.pointCode) ContactRationalGadget.pointCode scalePoint := by
  let q := Procedure.first ratCode ContactRationalGadget.pointCode
  let p := Procedure.second ratCode ContactRationalGadget.pointCode
  let a := (Procedure.first ratCode ratCode).comp p
  let b := (Procedure.second ratCode ratCode).comp p
  exact (Procedure.ratMul.comp (q.pair a)).pair (Procedure.ratMul.comp (q.pair b))

def scaledPositions (x : ℚ × Input) : List (ℚ × ℚ) :=
  (positions x.2).map (fun p => (x.1 * p.1, x.1 * p.2))

noncomputable opaque scaledProgram : Procedure scaledInputCode
    (listCode ContactRationalGadget.pointCode) scaledPositions :=
  (Procedure.listMapWith (ea := ratCode) (eb := ContactRationalGadget.pointCode)
    (ec := ContactRationalGadget.pointCode) (f := fun q p => (q * p.1, q * p.2))
      (0, 0) (0, 0) scalePointProgram).comp
        ((Procedure.first ratCode inputCode).pair
          (program.comp (Procedure.second ratCode inputCode)))

noncomputable def scaledCertificate : Turing.TM2ComputableInPolyTime scaledInputCode
    (listCode ContactRationalGadget.pointCode) scaledPositions := scaledProgram.toTM2

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
