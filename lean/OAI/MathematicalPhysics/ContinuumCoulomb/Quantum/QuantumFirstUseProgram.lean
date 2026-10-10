import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateCode
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUse
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackListMapWith
import OAI.Computability.QuantumFactoring.BitStackTabulate

namespace OAI

/-! Literal first-use indices for the actual circuit gates. The fold stores a
unary index bounded by the gate-list length, including the no-use case. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFirstUseProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev TouchInput := ℕ × (ℕ × QMAGate)
def touchCode : TouchInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits gateCode)

def touches (x : TouchInput) : Bool :=
  decide (gateLeft x.2.2 % (x.1+1)=x.2.1) ||
    decide (gateRight x.2.2 % (x.1+1)=x.2.1)

theorem touches_spec (c : QMACircuit) (i : Fin (c.work+1)) (g : QMAGate) :
    touches (c.work,i.val,g)=decide (i ∈ qmaGateSites c.work g) := by
  apply Bool.eq_iff_iff.mpr
  have ht (x : TouchInput) : touches x = true ↔
      gateLeft x.2.2 % (x.1+1)=x.2.1 ∨ gateRight x.2.2 % (x.1+1)=x.2.1 := by
    unfold touches
    rw [Bool.or_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  rw [ht,decide_eq_true_eq]
  cases g <;>
    simp only [gateLeft,gateRight,qmaGateSites,Finset.mem_singleton,
      Finset.mem_insert,Fin.ext_iff,qmaQubit] <;>
    omega

noncomputable def touchesProgram : Procedure touchCode Procedure.boolCode touches := by
  let work := Procedure.first Nat.bits (prodCode Nat.bits gateCode)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits gateCode)
  let site := (Procedure.first Nat.bits gateCode).comp rest
  let gate := (Procedure.second Nat.bits gateCode).comp rest
  let modulus := Procedure.successor.comp work
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  exact Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (left.pair site)).pair
      (Procedure.binaryEq.comp (right.pair site)))

def step (x : Bool × ℕ) : ℕ := if x.1 then 0 else x.2+1

theorem step_le (b : Bool) (n : ℕ) : step (b,n) ≤ n+1 := by
  cases b <;> simp [step]

theorem fold_le (xs : List Bool) (n : ℕ) :
    xs.foldl (fun k b => step (b,k)) n ≤ xs.length+n := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    have h := ih (step (b,n))
    have hs := step_le b n
    simp only [List.foldl_cons,List.length_cons]
    omega

def first (xs : List Bool) : ℕ := xs.foldr (fun b n => step (b,n)) 0

theorem first_eq_findIdx (xs : List Bool) : first xs=xs.findIdx id := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [first,step,List.findIdx_cons,← ih,Nat.add_comm]

noncomputable def stepProgram :
    Procedure (prodCode Procedure.boolCode unaryCode) unaryCode step :=
  (Procedure.conditional (Procedure.first Procedure.boolCode unaryCode)
    (Procedure.constant _ unaryCode 0)
    (Procedure.unarySuccessor.comp (Procedure.second Procedure.boolCode unaryCode))).congrFun
      (by intro x; rfl)

noncomputable def foldProgram :
    Procedure (prodCode (listCode Procedure.boolCode) unaryCode) unaryCode
      (fun x => x.1.foldl (fun n b => step (b,n)) x.2) :=
  Procedure.foldList false stepProgram Polynomial.X (by
    intro xs n i
    have h := fold_le (xs.take i) n
    have ht := List.length_take_le' i xs
    have hs := list_length_le_code Procedure.boolCode xs
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)

noncomputable def firstProgram :
    Procedure (listCode Procedure.boolCode) unaryCode first :=
  (foldProgram.comp ((Procedure.listReverse Procedure.boolCode false).pair
    (Procedure.constant _ unaryCode 0))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,first])

abbrev Input := QMACircuit × ℕ
def inputCode : Input → List Bool := prodCode circuitCode Nat.bits

def touchList (x : Input) : List Bool :=
  x.1.gates.map (fun g => touches (x.1.work,x.2,g))

def value : Input → ℕ := first ∘ touchList

noncomputable def touchListProgram : Procedure inputCode
    (listCode Procedure.boolCode) touchList := by
  let circuit := Procedure.first circuitCode Nat.bits
  let site := Procedure.second circuitCode Nat.bits
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let env := work.pair site
  let test : Procedure (prodCode (prodCode Nat.bits Nat.bits) gateCode)
      Procedure.boolCode (fun x => touches (x.1.1,x.1.2,x.2)) := by
    let context := Procedure.first (prodCode Nat.bits Nat.bits) gateCode
    exact touchesProgram.comp
      (((Procedure.first Nat.bits Nat.bits).comp context).pair
        (((Procedure.second Nat.bits Nat.bits).comp context).pair
          (Procedure.second (prodCode Nat.bits Nat.bits) gateCode)))
  exact (Procedure.listMapWith (f := fun e g => touches (e.1,e.2,g))
    (.hadamard 0) false test).comp (env.pair (gatesProgram.comp circuit))

noncomputable def program : Procedure inputCode unaryCode value :=
  firstProgram.comp touchListProgram

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode unaryCode value :=
  program.toTM2

theorem value_eq (c : QMACircuit) (i : Fin (c.work+1)) :
    value (c,i.val)=qmaFirstUse c i := by
  unfold value touchList
  simp only [Function.comp_apply]
  rw [first_eq_findIdx,List.findIdx_map]
  unfold qmaFirstUse
  congr 1
  funext g
  exact touches_spec c i g

def allValues (c : QMACircuit) : List ℕ :=
  (List.range (c.work+1)).map (fun i => value (c,i))

noncomputable def allProgram : Procedure circuitCode (listCode unaryCode) allValues := by
  let entry : Procedure (prodCode unaryCode circuitCode) unaryCode
      (fun x => value (x.2,x.1)) :=
    program.comp ((Procedure.second unaryCode circuitCode).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)))
  exact (Procedure.tabulate (f := fun c i => value (c,i)) 0 entry).comp
    ((Procedure.unarySuccessor.comp workProgram).pair (Procedure.identity circuitCode))

theorem allValues_eq (c : QMACircuit) :
    allValues c=List.ofFn (fun i : Fin (c.work+1) => qmaFirstUse c i) := by
  apply List.ext_getElem
  · simp only [allValues,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [allValues,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact value_eq c ⟨i,by simpa only [List.length_ofFn] using hj⟩

end ContinuumCoulomb.QuantumFirstUseProgram

end

end OAI
