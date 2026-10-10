import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathScaleProgram

namespace OAI

/-! Exact rational calibration for the ordered fork list. The perturbation
scale includes the unpaired active ports in its retained-energy bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

noncomputable def countProgram : Procedure stateCode unaryCode Prod.fst := Procedure.first _ _

noncomputable def bondsProgram : Procedure stateCode (listCode MediatorListProgram.bondCode)
    (fun s => s.2.1) :=
  (Procedure.first (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
    (Procedure.second unaryCode
      (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)))

noncomputable def scalarProgram : Procedure stateCode ratCode (fun s => s.2.2.1) :=
  (Procedure.first ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
      (Procedure.second unaryCode
        (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))))

noncomputable def groupsProgram : Procedure stateCode groupsCode (fun s => s.2.2.2) :=
  (Procedure.second ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp
      (Procedure.second unaryCode
        (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))))

noncomputable def leftWeight : Procedure pairCode ratCode (fun p => p.1.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.first portCode portCode)
noncomputable def rightWeight : Procedure pairCode ratCode (fun p => p.2.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.second portCode portCode)

noncomputable def pairLinearProgram : Procedure pairCode ratCode pairLinear := by
  let a := MediatorProgram.absoluteProgram.comp leftWeight
  let b := MediatorProgram.absoluteProgram.comp rightWeight
  let two := Procedure.constant pairCode ratCode 2
  exact Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair
      (Procedure.ratMul.comp (two.pair a)))).pair (Procedure.ratMul.comp (two.pair b)))

noncomputable def pairSquareProgram : Procedure pairCode ratCode pairSquare := by
  let a := MediatorProgram.absoluteProgram.comp leftWeight
  let b := MediatorProgram.absoluteProgram.comp rightWeight
  exact QuantumRoutingCode.squareProgram (Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode 1).pair a)).pair b))

noncomputable def pairOffsetProgram : Procedure pairCode ratCode pairOffset := by
  let a := QuantumRoutingCode.squareProgram leftWeight
  let b := QuantumRoutingCode.squareProgram rightWeight
  let three := Procedure.constant pairCode ratCode 3
  exact Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((Procedure.constant pairCode ratCode (3/4)).pair
      (Procedure.ratMul.comp (three.pair a)))).pair (Procedure.ratMul.comp (three.pair b)))

abbrev ScaleInput := ℚ × State
def scaleCode : ScaleInput → List Bool := prodCode ratCode stateCode

noncomputable def scaleProgram : Procedure scaleCode ratCode (fun x => scale x.1 x.2) := by
  let n := Procedure.first ratCode stateCode
  let s := Procedure.second ratCode stateCode
  let c := scalarProgram.comp s
  let gs := groupsProgram.comp s
  let ps := (Procedure.listMap (0,((0,0),(0,0))) ((0,0),(0,0))
    (Procedure.second Nat.bits pairCode)).comp (catalogProgram.comp gs)
  let sumPairs (f : Pair → ℚ) (p : Procedure pairCode ratCode f) :=
    RationalSumProgram.sumProgram.comp ((Procedure.listMap ((0,0),(0,0)) 0 p).comp ps)
  let absRetained := (QuantumPathScaleProgram.sumMapProgram MediatorProgram.absoluteProgram).comp
    (retainedProgram.comp s)
  let b := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair absRetained)).pair
      (MediatorProgram.absoluteProgram.comp c))
  let a := Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair
    (sumPairs pairLinear pairLinearProgram))
  let d := Procedure.ratAdd.comp (b.pair
    (Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 12).pair (sumPairs pairSquare pairSquareProgram))))
  exact QuantumRoutingCode.scaleProgram.comp (a.pair (d.pair n))

end ContinuumCoulomb.QuantumForkList

end

end OAI
