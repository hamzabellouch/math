import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.BinaryEncoding
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePauli
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.GlobalSinglet
import Mathlib.Computability.TuringMachine.Computable

namespace OAI

/-! The promise-QMA interface for the Heisenberg source.
The verifier uses the fixed H,T,CNOT gate set, complex quantum witnesses,
ancillas initialized to zero, one output measurement and a polynomial-time
TM2 circuit generator. There is no condition outside either promise set. -/

namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker
open BinaryEncoding

inductive QMAGate where
  | hadamard (qubit : ℕ)
  | phaseT (qubit : ℕ)
  | controlledNot (control target : ℕ)
  deriving DecidableEq, Repr

def qmaGateEquiv : QMAGate ≃ ((ℕ ⊕ ℕ) ⊕ (ℕ × ℕ)) where
  toFun
    | .hadamard i => Sum.inl (Sum.inl i)
    | .phaseT i => Sum.inl (Sum.inr i)
    | .controlledNot i j => Sum.inr (i, j)
  invFun
    | Sum.inl (Sum.inl i) => .hadamard i
    | Sum.inl (Sum.inr i) => .phaseT i
    | Sum.inr (i, j) => .controlledNot i j
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with (i | i) | ⟨i, j⟩ <;> rfl

def qmaGateCodec : Codec QMAGate := BinaryEncoding.equiv
  (BinaryEncoding.sum (BinaryEncoding.sum natural natural) (pair natural natural)) qmaGateEquiv

structure QMACircuit where
  /-- The circuit has work + 1 qubits; the final qubit is measured. -/
  work : ℕ
  witness : ℕ
  gates : List QMAGate
  deriving DecidableEq, Repr

def qmaCircuitEquiv : QMACircuit ≃ (ℕ × (ℕ × List QMAGate)) where
  toFun c := (c.work, c.witness, c.gates)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨n, w, gs⟩; rfl

def qmaCircuitCodec : Codec QMACircuit := BinaryEncoding.equiv
  (pair natural (pair natural (BinaryEncoding.list qmaGateCodec))) qmaCircuitEquiv

def QMAGate.WellFormed (n : ℕ) : QMAGate → Prop
  | .hadamard i => i < n
  | .phaseT i => i < n
  | .controlledNot i j => i < n ∧ j < n ∧ i ≠ j

def QMACircuit.WellFormed (c : QMACircuit) : Prop :=
  c.witness ≤ c.work ∧ ∀ g ∈ c.gates, g.WellFormed (c.work + 1)

noncomputable section

/-- Exact algebraic Hadamard gate. -/
def qmaHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  bellScale • !![1, 1; 1, -1]

/-- T=diag(1,exp(i*pi/4)), written with its exact algebraic entries. -/
def qmaPhaseT : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, bellScale * (1 + Complex.I)]

def qmaQubit (work index : ℕ) : Fin (work + 1) :=
  ⟨index % (work + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def qmaControlledNot (work : ℕ) (control target : Fin (work + 1))
    (s : SourceSpinBasis (work + 1)) : SourceSpinBasis (work + 1) :=
  fun i => if i = target ∧ s control = 1 then Equiv.swap (0 : Fin 2) 1 (s i) else s i

def qmaGateMatrix (work : ℕ) : QMAGate →
    Matrix (SourceSpinBasis (work + 1)) (SourceSpinBasis (work + 1)) ℂ
  | .hadamard i => sourceTensor (work + 1)
      (fun k => if k = qmaQubit work i then qmaHadamard else 1)
  | .phaseT i => sourceTensor (work + 1)
      (fun k => if k = qmaQubit work i then qmaPhaseT else 1)
  | .controlledNot i j => fun s t =>
      if s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0

def qmaCircuitMatrix (c : QMACircuit) :
    Matrix (SourceSpinBasis (c.work + 1)) (SourceSpinBasis (c.work + 1)) ℂ :=
  c.gates.foldl (fun M g => qmaGateMatrix c.work g * M) 1

/-- The witness occupies the first witness qubits; every remaining qubit,
including the measured final qubit, starts in the zero state. -/
def qmaInitialState (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    SourceSpinBasis (c.work + 1) → ℂ :=
  fun s => if ∀ i : Fin (c.work + 1), c.witness ≤ i.val → s i = 0 then
    psi (fun i => s ⟨i.val, lt_of_lt_of_le i.isLt (hc.1.trans (Nat.le_succ _))⟩)
  else 0

/-- Born probability of measuring one on the output qubit. -/
def qmaAcceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) : ℝ :=
  ∑ s : SourceSpinBasis (c.work + 1),
    if s (Fin.last c.work) = 1 then
      Complex.normSq ((qmaCircuitMatrix c).mulVec (qmaInitialState c hc psi) s) else 0

structure QuantumVerifier where
  generate : BitString → QMACircuit
  uniform : Turing.TM2ComputableInPolyTime id qmaCircuitCodec.encode generate
  size : Polynomial ℕ
  size_bound : ∀ x, (generate x).work + (generate x).gates.length ≤ size.eval x.length
  wellFormed : ∀ x, (generate x).WellFormed

structure PromiseProblem (α : Type) where
  yes : Set α
  no : Set α
  disjoint : Disjoint yes no

section

theorem inQMA_two_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

theorem inQMA_three_atLeastTwo : Nat.AtLeastTwo (2 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 2 (@Nat.instNeZeroSucc 1)

attribute [local instance] inQMA_two_atLeastTwo inQMA_three_atLeastTwo

/-- Promise-QMA with completeness 2/3 and soundness 1/3. -/
def InQMA (P : PromiseProblem BitString) : Prop :=
  ∃ V : QuantumVerifier,
    (∀ x ∈ P.yes, ∃ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 ∧ 2 / 3 ≤ qmaAcceptance (V.generate x) (V.wellFormed x) psi) ∧
    (∀ x ∈ P.no, ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 → qmaAcceptance (V.generate x) (V.wellFormed x) psi ≤ 1 / 3)

end

/-- Actual polynomial-time many-one reduction with both promise maps. -/
structure PolynomialManyOne {α β : Type} (ea : α → BitString) (eb : β → BitString)
    (P : PromiseProblem α) (Q : PromiseProblem β) where
  map : α → β
  polynomialTime : Turing.TM2ComputableInPolyTime ea eb map
  maps_yes : ∀ x ∈ P.yes, map x ∈ Q.yes
  maps_no : ∀ x ∈ P.no, map x ∈ Q.no

def QMAHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InQMA P → Nonempty (PolynomialManyOne id encoding P Q)

/-- The machine-based definition includes the identity reduction. -/
def PolynomialManyOne.refl {α : Type} (ea : α → BitString) (P : PromiseProblem α) :
    PolynomialManyOne ea ea P P where
  map := id
  polynomialTime := Turing.idComputableInPolyTime ea
  maps_yes _ h := h
  maps_no _ h := h

end
end ContinuumCoulomb

end OAI
