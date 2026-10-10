import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNext

namespace OAI

/-! Literal lookup, parity and rational coefficient programs for the
initial odd subdivision. Endpoint queries read the actual input bond list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def initialLookupCode : (ℕ × List Bond) → List Bool :=
  prodCode Nat.bits (listCode bondCode)

noncomputable def initialBondProgram : Procedure initialLookupCode bondCode
    (fun x => initialBond x.2 x.1) := by
  let j := Procedure.first Nat.bits (listCode bondCode)
  let bs := Procedure.second Nat.bits (listCode bondCode)
  let i := Procedure.binaryDiv.comp (j.pair (Procedure.constant initialLookupCode Nat.bits 2))
  exact (Procedure.listGet bondCode (0,0,0)).comp (i.pair bs)

noncomputable def initialParityProgram : Procedure Nat.bits Procedure.boolCode
    (fun j => decide (j%2=0)) :=
  Procedure.binaryZero.comp (Procedure.binaryMod.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2)))

noncomputable def initialEndpointProgram : Procedure initialLookupCode Nat.bits
    (fun x => initialEndpoint x.2 x.1) := by
  let p := initialParityProgram.comp (Procedure.first Nat.bits (listCode bondCode))
  let b := initialBondProgram
  let left := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp b
  let right := (Procedure.first Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp b)
  exact (Procedure.conditional p left right).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,initialEndpoint])

def initialWeightCode : (ℕ × (ℚ × List Bond)) → List Bool :=
  prodCode Nat.bits (prodCode ratCode (listCode bondCode))

noncomputable def initialWeightProgram : Procedure initialWeightCode ratCode
    (fun x => initialWeight x.2.2 x.2.1 x.1) := by
  let j := Procedure.first Nat.bits (prodCode ratCode (listCode bondCode))
  let tail := Procedure.second Nat.bits (prodCode ratCode (listCode bondCode))
  let r := (Procedure.first ratCode (listCode bondCode)).comp tail
  let bs := (Procedure.second ratCode (listCode bondCode)).comp tail
  let b := initialBondProgram.comp (j.pair bs)
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp b)
  let twice := Procedure.ratMul.comp ((Procedure.constant initialWeightCode ratCode 2).pair r)
  let odd := Procedure.ratMul.comp (twice.pair w)
  exact (Procedure.conditional (initialParityProgram.comp j) r odd).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,initialWeight])

def initialMatch (x : ℕ × (ℕ × List Bond)) : List ℕ :=
  if initialEndpoint x.2.2 x.1=x.2.1 then [x.1] else []

noncomputable def initialMatchProgram :
    Procedure (prodCode unaryCode initialLookupCode) (listCode Nat.bits) initialMatch := by
  let j := Procedure.unaryToBits.comp (Procedure.first unaryCode initialLookupCode)
  let env := Procedure.second unaryCode initialLookupCode
  let i := (Procedure.first Nat.bits (listCode bondCode)).comp env
  let bs := (Procedure.second Nat.bits (listCode bondCode)).comp env
  let endpoint := initialEndpointProgram.comp (j.pair bs)
  let same := Procedure.binaryEq.comp (endpoint.pair i)
  let one := (Procedure.listCons Nat.bits).comp
    (j.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact (Procedure.conditional same one (Procedure.constant _ (listCode Nat.bits) [])).congrFun
    (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,initialMatch,id_eq])

noncomputable def initialIndicesProgram : Procedure initialLookupCode (listCode Nat.bits)
    (fun x => initialIndices x.2 x.1) := by
  let bs := Procedure.second Nat.bits (listCode bondCode)
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let count := Procedure.unaryAdd.comp (len.pair len)
  let tab := (Procedure.tabulate (f := fun env j => initialMatch (j,env)) []
    initialMatchProgram).comp (count.pair (Procedure.identity initialLookupCode))
  refine ((QuantumRawExchange.flattenProgram Nat.bits 0).comp tab).congrFun ?_
  intro x
  change ((List.range (x.2.length+x.2.length)).map (fun j => initialMatch (j,x))).flatten=
    initialIndices x.2 x.1
  rw [show x.2.length+x.2.length=2*x.2.length by omega]
  unfold initialIndices
  generalize List.range (2*x.2.length)=js
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [initialMatch] at ih
    by_cases h : initialEndpoint x.2 j=x.1 <;> simp [initialMatch,h,ih]

noncomputable def initialPointProgram :
    Procedure (prodCode initialWeightCode Nat.bits) portCode
      (fun x => (x.1.1+x.2,initialWeight x.1.2.2 x.1.2.1 x.2)) := by
  let env := Procedure.first initialWeightCode Nat.bits
  let j := Procedure.second initialWeightCode Nat.bits
  let n := (Procedure.first Nat.bits (prodCode ratCode (listCode bondCode))).comp env
  let tail := (Procedure.second Nat.bits (prodCode ratCode (listCode bondCode))).comp env
  exact (Procedure.binaryAdd.comp (n.pair j)).pair (initialWeightProgram.comp (j.pair tail))

def initialGroupInputCode : (ℕ × (ℚ × (ℕ × List Bond))) → List Bool :=
  prodCode Nat.bits (prodCode ratCode initialLookupCode)

noncomputable def initialGroupProgram : Procedure initialGroupInputCode (listCode portCode)
    (fun x => initialGroup x.1 x.2.2.2 x.2.1 x.2.2.1) := by
  let n := Procedure.first Nat.bits (prodCode ratCode initialLookupCode)
  let tail := Procedure.second Nat.bits (prodCode ratCode initialLookupCode)
  let r := (Procedure.first ratCode initialLookupCode).comp tail
  let lookup := (Procedure.second ratCode initialLookupCode).comp tail
  let bs := (Procedure.second Nat.bits (listCode bondCode)).comp lookup
  let env := n.pair (r.pair bs)
  let js := initialIndicesProgram.comp lookup
  exact ((Procedure.listMapWith
    (f := fun (y : ℕ × (ℚ × List Bond)) (j : ℕ) =>
      (y.1+j,initialWeight y.2.2 y.2.1 j)) 0 (0,0) initialPointProgram).comp
      (env.pair js)).congrFun (by intro x; rfl)

def initialGroupsCode : (ℕ × (ℚ × List Bond)) → List Bool :=
  prodCode unaryCode (prodCode ratCode (listCode bondCode))

noncomputable def initialGroupAtProgram :
    Procedure (prodCode unaryCode initialGroupsCode) (listCode portCode)
      (fun x => initialGroup x.2.1 x.2.2.2 x.2.2.1 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode initialGroupsCode)
  let env := Procedure.second unaryCode initialGroupsCode
  let n := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode (prodCode ratCode (listCode bondCode))).comp env)
  let tail := (Procedure.second unaryCode (prodCode ratCode (listCode bondCode))).comp env
  let r := (Procedure.first ratCode (listCode bondCode)).comp tail
  let bs := (Procedure.second ratCode (listCode bondCode)).comp tail
  exact initialGroupProgram.comp (n.pair (r.pair (i.pair bs)))

noncomputable def initialGroupsProgram : Procedure initialGroupsCode groupsCode
    (fun x => (List.range x.1).map (initialGroup x.1 x.2.2 x.2.1)) := by
  let n := Procedure.first unaryCode (prodCode ratCode (listCode bondCode))
  exact (Procedure.tabulate
    (f := fun (x : ℕ × (ℚ × List Bond)) i => initialGroup x.1 x.2.2 x.2.1 i)
    [] initialGroupAtProgram).comp (n.pair (Procedure.identity initialGroupsCode))

end ContinuumCoulomb.QuantumForkList

end

end OAI
