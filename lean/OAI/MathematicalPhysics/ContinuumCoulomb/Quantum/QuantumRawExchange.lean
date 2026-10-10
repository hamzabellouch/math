import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeSampleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorListProgram

namespace OAI

/-! Raw, rational finite-list instructions for the four-spin compiler. -/

namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

abbrev Raw := (Bool × Bool) × ((ℕ × ℕ) × ((Bool × Bool) × ℚ))
def rawCode : Raw → List Bool :=
  prodCode (prodCode Procedure.boolCode Procedure.boolCode)
    (prodCode (prodCode Nat.bits Nat.bits) (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode))

def axis (a : Bool) : Fin 2 := if a then 0 else 1

def pack {n : ℕ} (t : QMAXZTerm n) (J : ℚ) : Raw :=
  match t with
  | .scalar => ((false,false),((0,0),((false,false),J)))
  | .field i a => ((false,true),((i,0),((decide (a = 0),false),J)))
  | .pair i j _ a b => ((true,false),((i,j),((decide (a = 0),decide (b = 0)),J)))

theorem axis_pack (a : Fin 2) : axis (decide (a = 0)) = a := by
  fin_cases a <;> rfl

abbrev Environment := ℕ × ℚ
def environmentCode : Environment → List Bool := prodCode unaryCode ratCode
abbrev Input := Environment × Raw
def inputCode : Input → List Bool := prodCode environmentCode rawCode

def field (k : ℕ) (i : ℕ) (a : Fin 2) (J : ℚ) : List Bond :=
  List.ofFn fun e : Fin 3 => (4*i,4*i+(qmaFieldEdgeRight e).val,fieldValue k a J e)

def cross (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ) : List Bond :=
  List.ofFn fun e : Fin 16 =>
    let pq := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e
    (4*i+pq.1.val,4*j+pq.2.val,crossValue k r a b J pq.1 pq.2)

def bonds (x : Input) : List Bond :=
  let k := x.1.1
  let r := x.1.2
  let t := x.2
  let i := t.2.1.1
  let j := t.2.1.2
  let a := axis t.2.2.1.1
  let b := axis t.2.2.1.2
  let J := t.2.2.2
  if t.1.1 then cross k r i j a b J ++
      field k i a (counterA k a b J) ++ field k j b (counterB k a b J)
  else if t.1.2 then field k i a J else []

def scalar (x : Input) : ℚ :=
  let t := x.2
  if t.1.1 then -offset x.1.1 (axis t.2.2.1.1) (axis t.2.2.1.2) t.2.2.2
  else if t.1.2 then -shiftValue (axis t.2.2.1.1) t.2.2.2 else t.2.2.2

theorem bonds_length (x : Input) : (bonds x).length ≤ 22 := by
  simp only [bonds]
  split <;> rename_i h
  · simp [cross,field]
  · split <;> simp [field]

theorem bonds_pack_length {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) :
    (bonds ((k,r),pack t J)).length =
      match t with | .scalar => 0 | .field .. => 3 | .pair .. => 22 := by
  cases t <;> simp [bonds,pack,field,cross]

end ContinuumCoulomb.QuantumRawExchange

end OAI
