import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAdjacentProgram

namespace OAI

/-! Literal nearest-neighbor gate compilation. All finite loops use the
unary work bound; malformed gate indices take the original singleton branch. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

abbrev NearestInput := ℕ × QMAGate
def nearestInputCode : NearestInput → List Bool := prodCode unaryCode gateCode

def forwardGuard (x : NearestInput) : Bool :=
  decide (gateLeft x.2+1 ≤ gateRight x.2 ∧ gateRight x.2 ≤ x.1)
def backwardGuard (x : NearestInput) : Bool :=
  decide (gateRight x.2+1 ≤ gateLeft x.2 ∧ gateLeft x.2 ≤ x.1)

def nearestValue (x : NearestInput) : List QMAGate :=
  if gateTag x.2=2 then
    if forwardGuard x then
      adjacentList (gateLeft x.2) (min x.1 (gateRight x.2-gateLeft x.2-1)) true
    else if backwardGuard x then
      adjacentList (gateRight x.2) (min x.1 (gateLeft x.2-gateRight x.2-1)) false
    else [x.2]
  else [x.2]

theorem nearestValue_eq (x : NearestInput) : nearestValue x=qmaNearestGate x.1 x.2 := by
  rcases x with ⟨work,g⟩
  cases g with
  | hadamard i => rfl
  | phaseT i => rfl
  | controlledNot i j =>
    by_cases h : i < j ∧ j < work+1
    · have hg : forwardGuard (work,.controlledNot i j)=true := by
        change decide (i+1 ≤ j ∧ j ≤ work) = true
        simp only [decide_eq_true_eq]
        omega
      have hd : j-i-1 ≤ work := by omega
      simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true,hg,min_eq_right hd,
        qmaNearestGate,dite_eq_left h]
      exact (adjacentList_eq work i (j-i-1) (by omega) true).symm
    · have hg : forwardGuard (work,.controlledNot i j)=false := by
        change decide (i+1 ≤ j ∧ j ≤ work) = false
        simp only [decide_eq_false_iff_not]
        omega
      by_cases h' : j < i ∧ i < work+1
      · have hr : backwardGuard (work,.controlledNot i j)=true := by
          change decide (j+1 ≤ i ∧ i ≤ work) = true
          simp only [decide_eq_true_eq]
          omega
        have hd : i-j-1 ≤ work := by omega
        simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true,hg,Bool.false_eq_true,ite_false,hr,min_eq_right hd,
          qmaNearestGate,dite_eq_right h,dite_eq_left h']
        exact (adjacentList_eq work j (i-j-1) (by omega) false).symm
      · have hr : backwardGuard (work,.controlledNot i j)=false := by
          change decide (j+1 ≤ i ∧ i ≤ work) = false
          simp only [decide_eq_false_iff_not]
          omega
        simp only [nearestValue,gateTag,gateLeft,gateRight,ite_true,hg,hr,Bool.false_eq_true,ite_false,
          qmaNearestGate,dite_eq_right h,dite_eq_right h']

private noncomputable def workBits : Procedure nearestInputCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode gateCode)
private noncomputable def leftBits : Procedure nearestInputCode Nat.bits (fun x => gateLeft x.2) :=
  gateLeftProgram.comp (Procedure.second unaryCode gateCode)
private noncomputable def rightBits : Procedure nearestInputCode Nat.bits (fun x => gateRight x.2) :=
  gateRightProgram.comp (Procedure.second unaryCode gateCode)

noncomputable def forwardGuardProgram : Procedure nearestInputCode Procedure.boolCode forwardGuard :=
  (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp ((Procedure.successor.comp leftBits).pair rightBits)).pair
      (Procedure.binaryLe.comp (rightBits.pair workBits)))).congrFun (by
        intro x
        simp [forwardGuard,Function.comp_apply])

noncomputable def backwardGuardProgram : Procedure nearestInputCode Procedure.boolCode backwardGuard :=
  (Procedure.boolAnd.comp
    ((Procedure.binaryLe.comp ((Procedure.successor.comp rightBits).pair leftBits)).pair
      (Procedure.binaryLe.comp (leftBits.pair workBits)))).congrFun (by
        intro x
        simp [backwardGuard,Function.comp_apply])

noncomputable def nearestProgram : Procedure nearestInputCode (listCode gateCode) nearestValue := by
  let work := Procedure.first unaryCode gateCode
  let gate := Procedure.second unaryCode gateCode
  let one := (Procedure.listCons gateCode).comp
    (gate.pair (Procedure.constant nearestInputCode (listCode gateCode) []))
  let dForward := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (rightBits.pair leftBits)).pair
      (Procedure.constant nearestInputCode Nat.bits 1))
  let dBackward := Procedure.binarySub.comp
    ((Procedure.binarySub.comp (leftBits.pair rightBits)).pair
      (Procedure.constant nearestInputCode Nat.bits 1))
  let forward := adjacentProgram.comp ((Procedure.clippedUnary.comp (work.pair dForward)).pair
    (leftBits.pair (Procedure.constant nearestInputCode Procedure.boolCode true)))
  let backward := adjacentProgram.comp ((Procedure.clippedUnary.comp (work.pair dBackward)).pair
    (rightBits.pair (Procedure.constant nearestInputCode Procedure.boolCode false)))
  let cnot := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant nearestInputCode Nat.bits 2))
  exact (Procedure.conditional cnot
    (Procedure.conditional forwardGuardProgram forward
      (Procedure.conditional backwardGuardProgram backward one)) one).congrFun (by
        intro x
        simp only [nearestValue,Function.comp_apply,decide_eq_true_eq])

noncomputable def nearestListProgram :
    Procedure circuitCode (listCode gateCode) (fun c => c.gates.flatMap (qmaNearestGate c.work)) := by
  let rows := Procedure.listMapWith (ea := unaryCode) (eb := gateCode) (ec := listCode gateCode)
    (f := fun work g => nearestValue (work,g)) (.hadamard 0) [] nearestProgram
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (rows.comp (workProgram.pair gatesProgram))).congrFun (by
      intro c
      simp only [Function.comp_apply,List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro g _
      exact nearestValue_eq (c.work,g))

noncomputable def nearestCircuitProgram : Procedure circuitCode circuitCode qmaNearestCircuit :=
  (workProgram.pair (witnessProgram.pair nearestListProgram)).result (by intro c; rfl)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
