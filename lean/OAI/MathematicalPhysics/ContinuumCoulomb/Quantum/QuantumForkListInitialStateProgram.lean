import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialProgram

namespace OAI

/-! A literal polynomial program emits the complete initial odd-subdivision
state, with its rational scale, singlet bonds and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev InitialInput := ℚ × (ℕ × (List Bond × ℚ))
def initialInputCode : InitialInput → List Bool :=
  prodCode ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))

noncomputable def initialInputCount : Procedure initialInputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp
    (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode)))

noncomputable def initialInputBonds : Procedure initialInputCode (listCode bondCode)
    (fun x => x.2.2.1) :=
  (Procedure.first (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp
      (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))))

noncomputable def initialInputConstant : Procedure initialInputCode ratCode (fun x => x.2.2.2) :=
  (Procedure.second (listCode bondCode) ratCode).comp
    ((Procedure.second unaryCode (prodCode (listCode bondCode) ratCode)).comp
      (Procedure.second ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))))

noncomputable def initialBondWeight : Procedure bondCode ratCode (fun b => b.2.2) :=
  (Procedure.second Nat.bits ratCode).comp (Procedure.second Nat.bits (prodCode Nat.bits ratCode))

noncomputable def initialScaleProgram : Procedure initialInputCode ratCode
    (fun x => initialScale x.1 x.2.2.1 x.2.2.2) := by
  let n := Procedure.first ratCode (prodCode unaryCode (prodCode (listCode bondCode) ratCode))
  let ws := (Procedure.listMap (0,0,0) 0 initialBondWeight).comp initialInputBonds
  let input := (n.pair initialInputConstant).pair
    ((Procedure.constant initialInputCode (listCode ratCode) []).pair ws)
  exact (QuantumPathScaleProgram.program.comp input).congrFun (by
    intro x
    simp only [Function.comp_apply,QuantumPathScaleProgram.value,QuantumPathScaleProgram.active,
      QuantumPathScaleProgram.correction,QuantumPathScaleProgram.base,List.map_nil,List.sum_nil,
      mul_zero,zero_add,List.map_map,Function.comp_def,QuantumPathScaleProgram.linearCost,
      QuantumPathScaleProgram.squareCost,initialScale])

noncomputable def initialOffsetProgram : Procedure bondCode ratCode
    (fun b => 3/4+3*b.2.2^2) :=
  Procedure.ratAdd.comp ((Procedure.constant bondCode ratCode (3/4)).pair
    (Procedure.ratMul.comp ((Procedure.constant bondCode ratCode 3).pair
      (QuantumRoutingCode.squareProgram initialBondWeight))))

noncomputable def initialSingletProgram :
    Procedure (prodCode unaryCode portCode) bondCode
      (fun x => (x.2.1+2*x.1,x.2.1+2*x.1+1,x.2.2^2)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode portCode)
  let env := Procedure.second unaryCode portCode
  let n := (Procedure.first Nat.bits ratCode).comp env
  let r := (Procedure.second Nat.bits ratCode).comp env
  let a := Procedure.binaryAdd.comp (n.pair (Procedure.binaryMul.comp
    ((Procedure.constant (prodCode unaryCode portCode) Nat.bits 2).pair i)))
  exact a.pair ((Procedure.successor.comp a).pair (QuantumRoutingCode.squareProgram r))

noncomputable def initialStateProgram : Procedure initialInputCode stateCode
    (fun x => initial x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  let n := initialInputCount
  let bs := initialInputBonds
  let c := initialInputConstant
  let r := initialScaleProgram
  let count := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let size := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (count.pair count)))
  let singlets := (Procedure.tabulate
    (f := fun (p : Port) i => (p.1+2*i,p.1+2*i+1,p.2^2)) (0,0,0)
      initialSingletProgram).comp (count.pair ((Procedure.unaryToBits.comp n).pair r))
  let offset := RationalSumProgram.sumProgram.comp
    ((Procedure.listMap (0,0,0) 0 initialOffsetProgram).comp bs)
  let countRat := Procedure.natToRat.comp (Procedure.unaryToBits.comp count)
  let penalty := Procedure.ratMul.comp
    ((Procedure.ratMul.comp ((Procedure.constant initialInputCode ratCode 3).pair countRat)).pair
      (QuantumRoutingCode.squareProgram r))
  let scalar := Procedure.ratAdd.comp ((Procedure.ratAdd.comp (c.pair offset)).pair penalty)
  let groups := initialGroupsProgram.comp (n.pair (r.pair bs))
  exact (size.pair (singlets.pair (scalar.pair groups))).congrFun (by
    intro x
    dsimp only [Function.comp_apply,initial]
    rw [two_mul]
    rfl)

end ContinuumCoulomb.QuantumForkList

end

end OAI
