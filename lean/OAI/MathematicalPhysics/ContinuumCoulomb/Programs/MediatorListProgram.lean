import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePrograms
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorIteration

namespace OAI

/-! Actual TM2 programs which emit the central and spoke bond lists of one
simultaneous mediator stage. The index arithmetic follows the same
`n + 2e + spin` vertex enumeration as the proved finite-spin construction. -/

namespace ContinuumCoulomb.MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Bond := ℕ × (ℕ × ℚ)

def bondCode : Bond → List Bool := prodCode Nat.bits (prodCode Nat.bits ratCode)

def zeroBond : Bond := (0, 0, 0)

abbrev Env := ℕ × (ℕ × (ℕ × ℕ))

def envCode : Env → List Bool := prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

abbrev IndexedBond := Env × (ℕ × Bond)

def indexedCode : IndexedBond → List Bool := prodCode envCode (prodCode unaryCode bondCode)

noncomputable def environment : Procedure indexedCode envCode Prod.fst := Procedure.first _ _

noncomputable def rProgram : Procedure indexedCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp environment

noncomputable def wProgram : Procedure indexedCode unaryCode (fun x => x.1.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp environment

noncomputable def gProgram : Procedure indexedCode unaryCode (fun x => x.1.2.2.1) :=
  (((Procedure.first _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)).comp environment

noncomputable def nProgram : Procedure indexedCode unaryCode (fun x => x.1.2.2.2) :=
  (((Procedure.second _ _).comp (Procedure.second _ _)).comp (Procedure.second _ _)).comp environment

noncomputable def indexProgram : Procedure indexedCode Nat.bits (fun x => x.2.1) :=
  Procedure.unaryToBits.comp ((Procedure.first _ _).comp (Procedure.second _ _))

noncomputable def bondProgram : Procedure indexedCode bondCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable def leftProgram : Procedure indexedCode Nat.bits (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp bondProgram

noncomputable def rightProgram : Procedure indexedCode Nat.bits (fun x => x.2.2.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp bondProgram

noncomputable def weightProgram : Procedure indexedCode ratCode (fun x => x.2.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp bondProgram

noncomputable def parametersProgram : Procedure indexedCode MediatorProgram.rawCode
    (fun x => (x.1.1, x.1.2.1, x.1.2.2.1, x.2.2.2.2)) :=
  rProgram.pair (wProgram.pair (gProgram.pair weightProgram))

noncomputable def amplitudeProgram : Procedure indexedCode ratCode
    (fun x => MediatorParameters.spoke x.1.1 x.1.2.1 x.1.2.2.1 x.2.2.2.2) :=
  (MediatorProgram.spokeProgram.comp parametersProgram).congrFun (by intro x; rfl)

noncomputable def halfProgram : Procedure indexedCode Nat.bits (fun x => x.2.1 / 2) :=
  Procedure.binaryDiv.comp (indexProgram.pair (Procedure.constant indexedCode Nat.bits 2))

noncomputable def evenProgram : Procedure indexedCode Procedure.boolCode (fun x => decide (x.2.1 % 2 = 0)) :=
  Procedure.binaryZero.comp (Procedure.binaryMod.comp
    (indexProgram.pair (Procedure.constant indexedCode Nat.bits 2)))

noncomputable def negativeProgram : Procedure indexedCode Procedure.boolCode
    (fun x => decide (x.2.2.2.2 < 0)) :=
  (Procedure.intSign.comp (Procedure.ratNum.comp weightProgram)).congrFun (by
    intro x
    simp only [Function.comp_apply]
    simp only [Rat.num_neg])

noncomputable def spokeLeftProgram : Procedure indexedCode Nat.bits
    (fun x => if x.2.1 % 2 = 0 then x.2.2.1 else x.2.2.2.1) :=
  (Procedure.conditional evenProgram leftProgram rightProgram).congrFun (by intro x; simp)

noncomputable def vertexBaseProgram : Procedure indexedCode Nat.bits
    (fun x => x.1.2.2.2 + 2 * (x.2.1 / 2)) :=
  Procedure.binaryAdd.comp ((Procedure.unaryToBits.comp nProgram).pair
    (Procedure.binaryMul.comp ((Procedure.constant indexedCode Nat.bits 2).pair halfProgram)))

noncomputable def spokeRightProgram : Procedure indexedCode Nat.bits
    (fun x => x.1.2.2.2 + 2 * (x.2.1 / 2) +
      if x.2.1 % 2 = 0 then 0 else if x.2.2.2.2 < 0 then 0 else 1) := by
  let zero := Procedure.constant indexedCode Nat.bits 0
  let one := Procedure.constant indexedCode Nat.bits 1
  let odd := Procedure.conditional negativeProgram zero one
  let member := Procedure.conditional evenProgram zero odd
  exact (Procedure.binaryAdd.comp (vertexBaseProgram.pair member)).congrFun (by intro x; simp)

def spoke (x : IndexedBond) : Bond :=
  (if x.2.1 % 2 = 0 then x.2.2.1 else x.2.2.2.1,
    x.1.2.2.2 + 2 * (x.2.1 / 2) +
      if x.2.1 % 2 = 0 then 0 else if x.2.2.2.2 < 0 then 0 else 1,
    MediatorParameters.spoke x.1.1 x.1.2.1 x.1.2.2.1 x.2.2.2.2)

noncomputable def spokeProgram : Procedure indexedCode bondCode spoke :=
  spokeLeftProgram.pair (spokeRightProgram.pair amplitudeProgram)

abbrev Input := Env × List Bond

def inputCode : Input → List Bool := prodCode envCode (listCode bondCode)

abbrev LoopInput := ℕ × Input

def loopCode : LoopInput → List Bool := prodCode unaryCode inputCode

noncomputable def loopIndex : Procedure loopCode unaryCode Prod.fst := Procedure.first _ _

noncomputable def loopInput : Procedure loopCode inputCode Prod.snd := Procedure.second _ _

noncomputable def loopEnvironment : Procedure loopCode envCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp loopInput

noncomputable def loopEdges : Procedure loopCode (listCode bondCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp loopInput

noncomputable def loopBond : Procedure loopCode bondCode
    (fun x => (x.2.2.drop (x.1 / 2)).headD zeroBond) :=
  (Procedure.listGet bondCode zeroBond).comp
    ((Procedure.binaryDiv.comp ((Procedure.unaryToBits.comp loopIndex).pair
      (Procedure.constant loopCode Nat.bits 2))).pair loopEdges)

noncomputable def loopSpoke : Procedure loopCode bondCode
    (fun x => spoke (x.2.1, x.1, (x.2.2.drop (x.1 / 2)).headD zeroBond)) :=
  spokeProgram.comp (loopEnvironment.pair (loopIndex.pair loopBond))

def spokes (x : Input) : List Bond := (List.range (2 * x.2.length)).map
  (fun i => spoke (x.1, i, (x.2.drop (i / 2)).headD zeroBond))

noncomputable def spokesProgram : Procedure inputCode (listCode bondCode) spokes := by
  let len : Procedure inputCode unaryCode (fun x => x.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp (Procedure.second _ _)
  let twice := Procedure.unaryAdd.comp (len.pair len)
  exact ((Procedure.tabulate (ea := inputCode) (eb := bondCode)
      (f := fun (x : Input) i => spoke (x.1, i, (x.2.drop (i / 2)).headD zeroBond)) zeroBond loopSpoke).comp
    (twice.pair (Procedure.identity inputCode))).congrFun (by intro x; simp only [Function.comp_apply, id_eq, spokes]; congr 2; omega)

noncomputable def centralBase : Procedure loopCode Nat.bits (fun x => x.2.1.2.2.2 + 2 * x.1) := by
  let n := (((Procedure.second unaryCode unaryCode).comp
    (Procedure.second unaryCode (prodCode unaryCode unaryCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode)))).comp loopEnvironment
  exact Procedure.binaryAdd.comp ((Procedure.unaryToBits.comp n).pair
    (Procedure.binaryMul.comp ((Procedure.constant loopCode Nat.bits 2).pair
      (Procedure.unaryToBits.comp loopIndex))))

noncomputable def centralWeight : Procedure loopCode ratCode
    (fun x => (MediatorParameters.delta x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 : ℚ)) := by
  let r : Procedure loopCode unaryCode (fun x => x.2.1.1) :=
    (Procedure.first unaryCode _).comp loopEnvironment
  let rest : Procedure loopCode (prodCode unaryCode (prodCode unaryCode unaryCode))
      (fun x => x.2.1.2) := (Procedure.second unaryCode _).comp loopEnvironment
  let w : Procedure loopCode unaryCode (fun x => x.2.1.2.1) :=
    (Procedure.first unaryCode _).comp rest
  let g : Procedure loopCode unaryCode (fun x => x.2.1.2.2.1) :=
    ((Procedure.first unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp rest
  let params : Procedure loopCode MediatorProgram.rawCode
      (fun x => (x.2.1.1, x.2.1.2.1, x.2.1.2.2.1, 0)) :=
    r.pair (w.pair (g.pair (Procedure.constant loopCode ratCode 0)))
  exact (MediatorProgram.deltaRationalProgram.comp params).congrFun (by intro x; rfl)

def central (x : Input) : List Bond := (List.range x.2.length).map (fun i =>
  (x.1.2.2.2 + 2 * i, x.1.2.2.2 + 2 * i + 1,
    (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ)))

noncomputable def centralProgram : Procedure inputCode (listCode bondCode) central := by
  let len : Procedure inputCode unaryCode (fun x => x.2.length) :=
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp (Procedure.second _ _)
  let edge : Procedure loopCode bondCode (fun x =>
      (x.2.1.2.2.2 + 2 * x.1, x.2.1.2.2.2 + 2 * x.1 + 1,
        (MediatorParameters.delta x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 : ℚ))) :=
    centralBase.pair ((Procedure.successor.comp centralBase).pair centralWeight)
  exact ((Procedure.tabulate (ea := inputCode) (eb := bondCode)
      (f := fun (x : Input) i => (x.1.2.2.2 + 2 * i, x.1.2.2.2 + 2 * i + 1,
        (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ))) zeroBond edge).comp
    (len.pair (Procedure.identity inputCode))).congrFun (by intro x; rfl)

noncomputable def stageProgram : Procedure inputCode (listCode bondCode)
    (fun x => central x ++ spokes x) :=
  (Procedure.listAppend bondCode zeroBond).comp (centralProgram.pair spokesProgram)

noncomputable def encodedBondTuple : Procedure binaryHeisenbergEdgeCodec.encode
    (prodCode BinaryEncoding.natural.encode
      (BinaryEncoding.pair BinaryEncoding.natural binaryRationalCodec).encode)
    binaryHeisenbergEdgeEquiv :=
  (SourcePrograms.pairInput _ _ PrefixPrograms.natural).precompose binaryHeisenbergEdgeEquiv

noncomputable def encodedBondLeft : Procedure binaryHeisenbergEdgeCodec.encode Nat.bits
    BinaryHeisenbergEdge.left :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp encodedBondTuple)

noncomputable def encodedBondRest : Procedure binaryHeisenbergEdgeCodec.encode
    (prodCode BinaryEncoding.natural.encode binaryRationalCodec.encode)
    (fun e => (e.right, e.coefficient)) :=
  (SourcePrograms.pairInput _ _ PrefixPrograms.natural).comp
    ((Procedure.second _ _).comp encodedBondTuple)

noncomputable def encodedBondRight : Procedure binaryHeisenbergEdgeCodec.encode Nat.bits
    BinaryHeisenbergEdge.right :=
  EncodingPrograms.naturalInput.comp ((Procedure.first _ _).comp encodedBondRest)

noncomputable def encodedBondWeight : Procedure binaryHeisenbergEdgeCodec.encode ratCode
    (fun e => e.coefficient.value) :=
  SourcePrograms.rationalValue.comp ((Procedure.second _ _).comp encodedBondRest)

noncomputable def encodedBond : Procedure binaryHeisenbergEdgeCodec.encode bondCode
    (fun e => (e.left, e.right, e.coefficient.value)) :=
  encodedBondLeft.pair (encodedBondRight.pair encodedBondWeight)

noncomputable def sourceBonds : Procedure binaryHeisenbergCodec.encode (listCode bondCode)
    (fun d => d.edges.map (fun e => (e.left, e.right, e.coefficient.value))) :=
  (Procedure.listMap ⟨0, 0, ⟨0, 1⟩⟩ zeroBond encodedBond).comp SourcePrograms.edges

noncomputable def stage_certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode bondCode) (fun x => central x ++ spokes x) := stageProgram.toTM2

end ContinuumCoulomb.MediatorListProgram

end OAI
