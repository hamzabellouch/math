import Mathlib

namespace OAI

/-! Deterministic polynomial-time construction of strong thin trees. -/

namespace StrongThinTree

structure MultiGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  loopless : ∀ e, left e ≠ right e

namespace MultiGraph

def cut {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  T.filter fun e => (G.left e ∈ S ∧ G.right e ∉ S) ∨
    (G.right e ∈ S ∧ G.left e ∉ S)

def Connected {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → (G.cut T S).Nonempty

def SpanningTree {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  G.Connected T ∧ ∀ e ∈ T, ¬ G.Connected (T.erase e)

def EdgeConnected {n m : ℕ} (G : MultiGraph n m) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    k ≤ (G.cut Finset.univ S).card

end MultiGraph
end StrongThinTree

namespace CurrentKS

def frame : List Bool → List Bool
  | [] => [true]
  | b :: bs => false :: b :: frame bs

def encodeNat (n : ℕ) : List Bool := frame (Computability.encodeNat n)

inductive StackAction where
  | stay
  | pop
  | push (bit : Bool)
  deriving DecidableEq

def StackAction.apply : StackAction → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

structure Instruction (k q : ℕ) where
  next : Option (Fin q)
  actions : Fin k → StackAction

def Instruction.halt (k q : ℕ) : Instruction k q := ⟨none, fun _ => .stay⟩

structure Machine where
  stackCount : ℕ
  states : ℕ
  initial : Fin states
  inputStack : Fin stackCount
  outputStack : Fin stackCount
  table : List (Instruction stackCount states)

structure Config (k q : ℕ) where
  state : Option (Fin q)
  «stacks» : Fin k → List Bool

def topCode : List Bool → ℕ
  | [] => 0
  | false :: _ => 1
  | true :: _ => 2

def headsCode : (k : ℕ) → (Fin k → List Bool) → ℕ
  | 0, _ => 0
  | k + 1, s => topCode (s 0) + 3 * headsCode k (fun j => s j.succ)

def Machine.step (M : Machine) (c : Config M.stackCount M.states) :
    Config M.stackCount M.states :=
  match c.state with
  | none => c
  | some q =>
    let instruction := M.table.getD
      (3 ^ M.stackCount * q.val + headsCode M.stackCount c.stacks)
      (Instruction.halt M.stackCount M.states)
    ⟨instruction.next, fun j => (instruction.actions j).apply (c.stacks j)⟩

def Machine.init (M : Machine) (input : List Bool) : Config M.stackCount M.states :=
  ⟨some M.initial, fun j => if j = M.inputStack then input else []⟩

def Machine.run (M : Machine) (input : List Bool) (fuel : ℕ) :
    Config M.stackCount M.states := (M.step^[fuel]) (M.init input)

end CurrentKS

namespace AlgorithmicThinTrees
open StrongThinTree

structure ExplicitInput where
  n : ℕ
  m : ℕ
  k : ℕ
  graph : MultiGraph n m

structure BinaryInput where
  n : ℕ
  p : ℕ
  k : ℕ
  left : Fin p → Fin n
  right : Fin p → Fin n
  ordered : ∀ i, left i < right i
  distinct : Function.Injective (fun i => (left i, right i))
  multiplicity : Fin p → ℕ

abbrev BinaryInput.Edge (x : BinaryInput) := Σ i : Fin x.p, Fin (x.multiplicity i)

noncomputable def BinaryInput.edgeEquiv (x : BinaryInput) :
    x.Edge ≃ Fin (Fintype.card x.Edge) := Fintype.equivFin x.Edge

noncomputable def BinaryInput.graph (x : BinaryInput) :
    MultiGraph x.n (Fintype.card x.Edge) where
  left e := x.left (x.edgeEquiv.symm e).1
  right e := x.right (x.edgeEquiv.symm e).1
  loopless e := ne_of_lt (x.ordered (x.edgeEquiv.symm e).1)

inductive Input where
  | explicit (x : ExplicitInput)
  | binary (x : BinaryInput)

def ExplicitInput.encode (x : ExplicitInput) : List Bool :=
  CurrentKS.encodeNat x.n ++ CurrentKS.encodeNat x.m ++ CurrentKS.encodeNat x.k ++
    (List.ofFn fun i : Fin x.m =>
      CurrentKS.encodeNat (x.graph.left i).val ++
      CurrentKS.encodeNat (x.graph.right i).val).flatten

def BinaryInput.encode (x : BinaryInput) : List Bool :=
  CurrentKS.encodeNat x.n ++ CurrentKS.encodeNat x.p ++ CurrentKS.encodeNat x.k ++
    (List.ofFn fun i : Fin x.p =>
      CurrentKS.encodeNat (x.left i).val ++ CurrentKS.encodeNat (x.right i).val ++
      CurrentKS.encodeNat (x.multiplicity i)).flatten

def Input.encode : Input → List Bool
  | .explicit x => false :: x.encode
  | .binary x => true :: x.encode

def Input.length (x : Input) : ℕ := x.encode.length

def Input.n : Input → ℕ
  | .explicit x => x.n
  | .binary x => x.n

def Valid : Input → Prop
  | .explicit x => 1 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k
  | .binary x => 1 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k

def ThinTree {n m : ℕ} (C : ℝ) (k : ℕ) (G : MultiGraph n m)
    (T : Finset (Fin m)) : Prop :=
  G.SpanningTree T ∧ ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ((G.cut T S).card : ℝ) ≤ C / (k : ℝ) * (G.cut Finset.univ S).card

def ExplicitInput.encodeEdges (x : ExplicitInput) (edges : List (Fin x.m)) : List Bool :=
  edges.flatMap (fun e => CurrentKS.encodeNat e.val)

def BinaryInput.encodeEdges (x : BinaryInput) (edges : List x.Edge) : List Bool :=
  edges.flatMap (fun e => CurrentKS.encodeNat e.1.val ++ CurrentKS.encodeNat e.2.val)

noncomputable def BinaryInput.selected (x : BinaryInput) (edges : List x.Edge) :
    Finset (Fin (Fintype.card x.Edge)) := edges.toFinset.map x.edgeEquiv.toEmbedding

def TreeOutput (C : ℝ) : Input → List Bool → Prop
  | .explicit x, bits => ∃ edges : List (Fin x.m), edges.Nodup ∧
      bits = x.encodeEdges edges ∧ ThinTree C x.k x.graph edges.toFinset
  | .binary x, bits => ∃ edges : List x.Edge, edges.Nodup ∧
      bits = x.encodeEdges edges ∧ ThinTree C x.k x.graph (x.selected edges)

def GoodOutput (C : ℝ) (x : Input) (bits : List Bool) : Prop :=
  TreeOutput C x bits ∧ (x.n = 1 → bits = [])

def AlgorithmicStrongThinTrees : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M : CurrentKS.Machine, ∃ a degree : ℕ, 0 < a ∧
    ∀ x : Input, Valid x →
      let result := M.run x.encode (a * (x.length + 1) ^ degree)
      result.state = none ∧ GoodOutput C x (result.stacks M.outputStack)

end AlgorithmicThinTrees

namespace AlgorithmicThinTrees

theorem algorithmic_strong_thin_trees : AlgorithmicStrongThinTrees := by
  sorry

end AlgorithmicThinTrees

end OAI
