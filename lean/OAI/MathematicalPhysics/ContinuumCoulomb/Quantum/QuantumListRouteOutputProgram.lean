import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteLattice

namespace OAI

/-! Fixed-round routing, canonical bond merging, and the final threshold
margin are one literal polynomial source-output program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open ExactQuantumFactoring.BitStackProgram

abbrev OutputInput := Input × (ℚ × (ℚ × ℚ))
def outputInputCode : OutputInput → List Bool :=
  prodCode inputCode QuantumLatticeSerialization.thresholdCode

def output (D : ℕ) (x : OutputInput) : BinaryHeisenberg :=
  latticeOutput (iterate x.1.1 D x.1.2) (x.2.1+x.2.2.2) (x.2.2.1-x.2.2.2)

noncomputable def outputProgram (D : ℕ) :
    Procedure outputInputCode binaryHeisenbergCodec.encode (output D) := by
  let x := Procedure.first inputCode QuantumLatticeSerialization.thresholdCode
  let t := Procedure.second inputCode QuantumLatticeSerialization.thresholdCode
  let a := (Procedure.first ratCode (prodCode ratCode ratCode)).comp t
  let be := (Procedure.second ratCode (prodCode ratCode ratCode)).comp t
  let b := (Procedure.first ratCode ratCode).comp be
  let e := (Procedure.second ratCode ratCode).comp be
  let lo := Procedure.ratAdd.comp (a.pair e)
  let hi := Procedure.ratSub.comp (b.pair e)
  exact latticeOutputProgram.comp (((iterateProgram D).comp x).pair (lo.pair hi))

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
