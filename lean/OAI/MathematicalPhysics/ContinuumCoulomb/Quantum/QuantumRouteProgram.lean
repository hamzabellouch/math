import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanRoute
import OAI.Computability.QuantumFactoring.Procedure

namespace OAI

/-! Literal polynomial programs for the lattice route length and each route point. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

abbrev Pair := ℕ × ℕ
def pairCode : Pair → List Bool := prodCode Nat.bits Nat.bits
abbrev AxisInput := Pair × ℕ
def axisCode : AxisInput → List Bool := prodCode pairCode Nat.bits

noncomputable opaque distanceProgram : Procedure pairCode Nat.bits (fun x => Nat.dist x.1 x.2) := by
  let a := Procedure.first Nat.bits Nat.bits
  let b := Procedure.second Nat.bits Nat.bits
  exact Procedure.binaryAdd.comp ((Procedure.binarySub.comp (a.pair b)).pair
    (Procedure.binarySub.comp (b.pair a)))

noncomputable opaque axisPairProgram : Procedure axisCode pairCode Prod.fst := Procedure.first _ _
noncomputable opaque axisStartProgram : Procedure axisCode Nat.bits (fun x => x.1.1) :=
  (Procedure.first _ _).comp axisPairProgram
noncomputable opaque axisEndProgram : Procedure axisCode Nat.bits (fun x => x.1.2) :=
  (Procedure.second _ _).comp axisPairProgram
noncomputable opaque axisCursorProgram : Procedure axisCode Nat.bits Prod.snd := Procedure.second _ _

noncomputable opaque axisProgram : Procedure axisCode Nat.bits (fun x => qmaAxisWalk x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (Procedure.binaryLe.comp (axisStartProgram.pair axisEndProgram))
    (Procedure.binaryAdd.comp (axisStartProgram.pair axisCursorProgram))
    (Procedure.binarySub.comp (axisStartProgram.pair axisCursorProgram))).congrFun
    (by intro x; simp [qmaAxisWalk])

abbrev RouteInput := (Pair × Pair) × ℕ
def routeCode : RouteInput → List Bool := prodCode (prodCode pairCode pairCode) Nat.bits
noncomputable opaque endsProgram : Procedure routeCode (prodCode pairCode pairCode) Prod.fst :=
  Procedure.first _ _
noncomputable opaque startProgram : Procedure routeCode pairCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp endsProgram
noncomputable opaque endProgram : Procedure routeCode pairCode (fun x => x.1.2) :=
  (Procedure.second _ _).comp endsProgram
noncomputable opaque cursorProgram : Procedure routeCode Nat.bits Prod.snd := Procedure.second _ _
noncomputable opaque startXProgram : Procedure routeCode Nat.bits (fun x => x.1.1.1) :=
  (Procedure.first _ _).comp startProgram
noncomputable opaque startYProgram : Procedure routeCode Nat.bits (fun x => x.1.1.2) :=
  (Procedure.second _ _).comp startProgram
noncomputable opaque endXProgram : Procedure routeCode Nat.bits (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp endProgram
noncomputable opaque endYProgram : Procedure routeCode Nat.bits (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp endProgram
noncomputable opaque horizontalLengthProgram : Procedure routeCode Nat.bits
    (fun x => Nat.dist x.1.1.1 x.1.2.1) :=
  distanceProgram.comp (startXProgram.pair endXProgram)
noncomputable opaque verticalLengthProgram : Procedure routeCode Nat.bits
    (fun x => Nat.dist x.1.1.2 x.1.2.2) :=
  distanceProgram.comp (startYProgram.pair endYProgram)
noncomputable opaque lengthProgram : Procedure routeCode Nat.bits
    (fun x => qmaManhattanLength x.1.1 x.1.2) :=
  Procedure.binaryAdd.comp (horizontalLengthProgram.pair verticalLengthProgram)

noncomputable opaque horizontalPointProgram : Procedure routeCode Nat.bits
    (fun x => qmaAxisWalk x.1.1.1 x.1.2.1 x.2) :=
  axisProgram.comp ((startXProgram.pair endXProgram).pair cursorProgram)
noncomputable opaque verticalPointProgram : Procedure routeCode Nat.bits
    (fun x => qmaAxisWalk x.1.1.2 x.1.2.2 (x.2-Nat.dist x.1.1.1 x.1.2.1)) :=
  axisProgram.comp ((startYProgram.pair endYProgram).pair
    (Procedure.binarySub.comp (cursorProgram.pair horizontalLengthProgram)))

noncomputable opaque pointProgram : Procedure routeCode pairCode
    (fun x => qmaManhattanPoint x.1.1 x.1.2 x.2) :=
  (Procedure.conditional (Procedure.binaryLe.comp (cursorProgram.pair horizontalLengthProgram))
    (horizontalPointProgram.pair startYProgram) (endXProgram.pair verticalPointProgram)).congrFun
    (by intro x; simp [qmaManhattanPoint])

noncomputable def pointCertificate : Turing.TM2ComputableInPolyTime routeCode pairCode
    (fun x => qmaManhattanPoint x.1.1 x.1.2 x.2) := pointProgram.toTM2
noncomputable def lengthCertificate : Turing.TM2ComputableInPolyTime routeCode Nat.bits
    (fun x => qmaManhattanLength x.1.1 x.1.2) := lengthProgram.toTM2

end ContinuumCoulomb.QuantumRouteCode

end

end OAI
