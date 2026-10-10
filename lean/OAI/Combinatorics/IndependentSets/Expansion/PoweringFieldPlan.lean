import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringRowData

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open IndependentSetsGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

theorem walkEnd_tailPorts (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
      walkEnd G v (tailPorts n p k) = (edgeAt G n (v, p) k).1 := by
  intro n
  induction n with
  | zero => intro v p k; rfl
  | succ n ih =>
      intro v p k
      refine Fin.cases rfl (fun j => ?_) k
      exact ih (next G v (p 0)) (fun i => p i.succ) j

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

theorem walkEnd_headPorts (G : PortGraph V D) (n : Nat) (v : V)
    (p : Fin (n + 1) → D) (k : Fin (n + 1)) :
    walkEnd G v (headPorts n p k) = (G.rot (edgeAt G n (v, p) k)).1 := by
  rw [headPorts, walkEnd_append, walkEnd_tailPorts]
  change (G.rot ((edgeAt G n (v, p) k).1, p k)).1 = _
  have hp : (edgeAt G n (v, p) k).2 = p k := edgeAt_port G n (v, p) k
  rw [← hp]

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

def evaluate {vertices d : Nat} (input : PortTables.Table vertices d)
    (start : Fin vertices) : Instruction d → Bool
  | .relation ports port a b => PortTables.accepts input
      (walkEnd (PortTables.portGraph input) start ports, port) a b
  | .equal left right => decide
      (walkEnd (PortTables.portGraph input) start left =
        walkEnd (PortTables.portGraph input) start right)

def fieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) : Field (slotCount d n) → Instruction d
  | .inl (a, b) => .relation (tailPorts n ports k) (ports k) a b
  | .inr (.inl i) => .equal (addressPorts i) (tailPorts n ports k)
  | .inr (.inr i) => .equal (List.ofFn ports ++ addressPorts i) (headPorts n ports k)

theorem evaluate_fieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (fieldPlan n ports k field) = walkData input n (start, ports) k field := by
  rcases field with ⟨a,b⟩ | i | i
  · simp only [evaluate, fieldPlan, walkData, walkEnd_tailPorts]
    have hp : (edgeAt (PortTables.portGraph input) n (start, ports) k).2 = ports k :=
      edgeAt_port (PortTables.portGraph input) n (start, ports) k
    rw [← hp]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_tailPorts]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input) start i
    rw [ha]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_append,
      walkEnd_headPorts]
    rw [← wordEnd_eq_walkEnd_ofFn]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input)
      (wordEnd (PortTables.portGraph input) (n + 1) start ports) i
    rw [ha]
    rfl

def directedFieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) : Instruction d :=
  fieldPlan n ports k (if direction then transposeField field else field)

theorem fieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (fieldPlan n ports k field).radius ≤ 2 * (n + 1) := by
  have hk := k.isLt
  rcases field with ⟨a,b⟩ | i | i
  · simp only [fieldPlan, Instruction.radius, tailPorts_length]
    omega
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, tailPorts_length]
    exact max_le (by omega) (by omega)
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, headPorts, List.length_append,
      List.length_ofFn, List.length_singleton, tailPorts_length]
    exact max_le (by omega) (by omega)

theorem directedFieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (directedFieldPlan n ports direction k field).radius ≤ 2 * (n + 1) :=
  fieldPlan_radius n ports k _

theorem evaluate_directedFieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (directedFieldPlan n ports direction k field) =
      rowData input n (direction, start, ports) k field :=
  evaluate_fieldPlan input n start ports k _

def rowPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Instruction d) :=
  List.ofFn fun i : Fin (inputSize (n + 1) (slotCount d n)) =>
    let pair := (inputEquiv (n + 1) (slotCount d n)).symm i
    directedFieldPlan n ports direction pair.1 pair.2

theorem evaluate_rowPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (rowPlan n ports direction).map (evaluate input start) =
      List.ofFn (rowBits input n (direction, start, ports)) := by
  rw [rowPlan, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [evaluate_directedFieldPlan, rowBits_packData]
  rfl

theorem dataTape_eq_plan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    dataTape input n (direction, start, ports) =
      encodeBits ((rowPlan n ports direction).map (evaluate input start)) := by
  rw [evaluate_rowPlan, dataTape_eq]

end IndependentSetsGames.Foundations.PCP.PoweringFieldPlan

end OAI
