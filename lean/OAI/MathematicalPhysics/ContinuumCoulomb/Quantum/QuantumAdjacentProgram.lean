import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateCode
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! The recursive adjacent-CNOT construction is a literal finite prefix,
one central gate, and its reversed prefix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def swapPrefix (a d : ℕ) : List QMAGate :=
  ((List.range d).map (fun k => swapList (a+k))).flatten

theorem swapPrefix_succ (a d : ℕ) :
    swapPrefix a (d+1)=swapList a++swapPrefix (a+1) d := by
  have hf : (fun k => swapList (a+Nat.succ k))=(fun k => swapList (a+1+k)) := by
    funext k
    congr 1
    omega
  simp only [swapPrefix,List.range_succ_eq_map,List.map_cons,List.flatten_cons,
    Nat.add_zero,List.map_map,Function.comp_def]
  rw [hf]

def adjacentList (a d : ℕ) (b : Bool) : List QMAGate :=
  swapPrefix a d++[qmaOrderedCnot (a+d) (a+d+1) b]++(swapPrefix a d).reverse

theorem adjacentList_eq (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    qmaAdjacentCnot work a d h b=adjacentList a d b := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    change swapList a++qmaAdjacentCnot work (a+1) d _ b++swapList a=adjacentList a (d+1) b
    rw [ih]
    unfold adjacentList
    rw [swapPrefix_succ,List.reverse_append,swapList_reverse]
    have ha : a+1+d=a+(d+1) := by omega
    rw [ha]
    simp only [List.append_assoc]

noncomputable def swapPrefixProgram :
    Procedure (prodCode unaryCode Nat.bits) (listCode gateCode)
      (fun x => swapPrefix x.2 x.1) := by
  let k := Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)
  let a := Procedure.second unaryCode Nat.bits
  let step := swapListProgram.comp (Procedure.binaryAdd.comp (a.pair k))
  let table := Procedure.tabulate (f := fun a k => swapList (a+k)) [] step
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp table).congrFun
    (by intro x; rfl)

noncomputable def orderedCnotProgram :
    Procedure (prodCode (prodCode Nat.bits Nat.bits) Procedure.boolCode) gateCode
      (fun x => qmaOrderedCnot x.1.1 x.1.2 x.2) := by
  let p := Procedure.first (prodCode Nat.bits Nat.bits) Procedure.boolCode
  let b := Procedure.second (prodCode Nat.bits Nat.bits) Procedure.boolCode
  let forward := cnotProgram.comp p
  let backward := cnotProgram.comp
    (((Procedure.second Nat.bits Nat.bits).comp p).pair
      ((Procedure.first Nat.bits Nat.bits).comp p))
  exact (Procedure.conditional b forward backward).congrFun (by intro x; rfl)

abbrev AdjacentInput := ℕ × (ℕ × Bool)
def adjacentInputCode : AdjacentInput → List Bool :=
  prodCode unaryCode (prodCode Nat.bits Procedure.boolCode)

noncomputable def adjacentProgram :
    Procedure adjacentInputCode (listCode gateCode)
      (fun x => adjacentList x.2.1 x.1 x.2.2) := by
  let d := Procedure.first unaryCode (prodCode Nat.bits Procedure.boolCode)
  let ab := Procedure.second unaryCode (prodCode Nat.bits Procedure.boolCode)
  let a := (Procedure.first Nat.bits Procedure.boolCode).comp ab
  let b := (Procedure.second Nat.bits Procedure.boolCode).comp ab
  let p := swapPrefixProgram.comp (d.pair a)
  let left := Procedure.binaryAdd.comp (a.pair (Procedure.unaryToBits.comp d))
  let right := Procedure.successor.comp left
  let center := orderedCnotProgram.comp ((left.pair right).pair b)
  let singleton := (Procedure.listCons gateCode).comp
    (center.pair (Procedure.constant adjacentInputCode (listCode gateCode) []))
  let first := (Procedure.listAppend gateCode (.hadamard 0)).comp (p.pair singleton)
  exact (Procedure.listAppend gateCode (.hadamard 0)).comp
    (first.pair ((Procedure.listReverse gateCode (.hadamard 0)).comp p))

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
