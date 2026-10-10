import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChain
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathVisitProgram
import OAI.Computability.QuantumFactoring.BitStackDivision

namespace OAI

/-! Literal evaluation of the physical port chain on a computed coarse path.
The output enumerates both endpoint centers and every incoming/outgoing port. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortChainProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def offset (p : Pair) (x y : ℕ) : Pair := (32*p.1+x,32*p.2+y)

noncomputable def offsetProgram (x y : ℕ) : Procedure pairCode pairCode
    (fun p => offset p x y) := by
  let coord (p : Procedure pairCode Nat.bits Prod.fst) (c : ℕ) :=
    Procedure.binaryAdd.comp
      ((Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 32).pair p)).pair
        (Procedure.constant pairCode Nat.bits c))
  let py := Procedure.second Nat.bits Nat.bits
  let vy := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 32).pair py)).pair
      (Procedure.constant pairCode Nat.bits y))
  exact (coord (Procedure.first Nat.bits Nat.bits) x).pair vy

def port (p : Pair) (a : ℕ) : Pair :=
  if a=0 then offset p 23 16 else if a=1 then offset p 16 23
  else if a=2 then offset p 9 16 else offset p 16 9

theorem port_fin (p : Pair) (a : Fin 4) : port p a.val = qmaGridPort p a := by
  fin_cases a <;> rfl

noncomputable def portProgram : Procedure (prodCode pairCode Nat.bits) pairCode
    (fun x => port x.1 x.2) := by
  let p := Procedure.first pairCode Nat.bits
  let a := Procedure.second pairCode Nat.bits
  let is (i : ℕ) := Procedure.binaryEq.comp (a.pair (Procedure.constant _ Nat.bits i))
  exact (Procedure.conditional (is 0) ((offsetProgram 23 16).comp p)
    (Procedure.conditional (is 1) ((offsetProgram 16 23).comp p)
      (Procedure.conditional (is 2) ((offsetProgram 9 16).comp p)
        ((offsetProgram 16 9).comp p)))).congrFun (by
          intro x
          simp only [Function.comp_apply,decide_eq_true_eq,port])

noncomputable def directedProgram : Procedure (prodCode pairCode pairCode) pairCode
    (fun x => qmaDirectedPort x.1 x.2) :=
  (portProgram.comp ((Procedure.first pairCode pairCode).pair
    QuantumPathVisitProgram.neighborIndexProgram)).congrFun (by
      intro x
      exact port_fin x.1 (qmaGridNeighborIndex x.1 x.2))

noncomputable def centerProgram : Procedure pairCode pairCode qmaExpandedPoint :=
  offsetProgram 16 16

noncomputable def neighborProgram : Procedure Nat.bits Nat.bits qmaPortNeighborIndex := by
  let half := Procedure.binaryDiv.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2))
  let parity := Procedure.binaryMod.comp
    ((Procedure.identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 2))
  let isOdd := Procedure.binaryEq.comp (parity.pair (Procedure.constant Nat.bits Nat.bits 1))
  let up := Procedure.binaryAdd.comp (half.pair (Procedure.constant Nat.bits Nat.bits 1))
  let down := Procedure.binarySub.comp (half.pair (Procedure.constant Nat.bits Nat.bits 1))
  exact (Procedure.conditional isOdd up down).congrFun (by
    intro k
    simp only [Function.comp_apply,id_eq,decide_eq_true_eq,qmaPortNeighborIndex])

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

def point (xs : List Pair) (k : ℕ) : Pair :=
  qmaPortChain (QuantumPathVisitProgram.lookup xs) (xs.length-1) k

noncomputable def lengthProgram : Procedure (listCode pairCode) unaryCode
    (fun xs => xs.length-1) :=
  Procedure.unarySub.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).pair
      (Procedure.constant (listCode pairCode) unaryCode 1))

noncomputable def pointProgram : Procedure inputCode pairCode (fun x => point x.2 x.1) := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))
  let xs := Procedure.second unaryCode (listCode pairCode)
  let len := Procedure.unaryToBits.comp (lengthProgram.comp xs)
  let last := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair len)).pair
      (Procedure.constant inputCode Nat.bits 1))
  let first := (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.constant inputCode Nat.bits 0).pair xs)
  let final := (Procedure.listGet pairCode (0,0)).comp (len.pair xs)
  let half := Procedure.binaryDiv.comp (k.pair (Procedure.constant inputCode Nat.bits 2))
  let here := (Procedure.listGet pairCode (0,0)).comp (half.pair xs)
  let there := (Procedure.listGet pairCode (0,0)).comp ((neighborProgram.comp k).pair xs)
  let inner := directedProgram.comp (here.pair there)
  exact (Procedure.conditional (Procedure.binaryZero.comp k) (centerProgram.comp first)
    (Procedure.conditional (Procedure.binaryEq.comp (k.pair last))
      (centerProgram.comp final) inner)).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,decide_eq_true_eq,point,qmaPortChain,
          qmaRoutePort,QuantumPathVisitProgram.lookup])

def value (xs : List Pair) : List Pair :=
  (List.range (2*(xs.length-1)+2)).map (point xs)

@[simp] theorem value_length (xs : List Pair) : (value xs).length = 2*(xs.length-1)+2 := by
  simp only [value,List.length_map,List.length_range]

noncomputable def program : Procedure (listCode pairCode) (listCode pairCode) value := by
  let n := Procedure.unaryAdd.comp
    ((Procedure.unaryMul.comp ((Procedure.constant (listCode pairCode) unaryCode 2).pair
      lengthProgram)).pair (Procedure.constant (listCode pairCode) unaryCode 2))
  exact (Procedure.tabulate (f := point) (0,0) pointProgram).comp
    (n.pair (Procedure.identity (listCode pairCode)))

end ContinuumCoulomb.QuantumPortChainProgram

end

end OAI
