import OAI.Combinatorics.SparsestCut.FiniteGraph
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.OfFn
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Encodings and reductions for uniform sparsest cut

These definitions express the polynomial-time reduction and approximation search problem in
*Constant-factor hardness of uniform sparsest cut* by OpenAI. The last semantic implication
uses rational threshold comparison.
-/

namespace UniformSparsestCut

abbrev BitString := List Bool

/-- A self-delimiting binary block: unary length, terminator, then the bits. -/
def block (s : BitString) : BitString := List.replicate s.length true ++ false :: s

/-- Binary, not unary, representation of a natural number, with a length prefix. -/
def encodeNat (n : ℕ) : BitString := block (Computability.encodeNat n)

/-- Signed numerator and positive denominator, both in binary. -/
def encodeRat (q : ℚ) : BitString :=
  decide (q.num < 0) :: (encodeNat q.num.natAbs ++ encodeNat q.den)

def encodePair (p : BitString × BitString) : BitString := block p.1 ++ p.2

def encodeBool (b : Bool) : BitString := [b]

/-- A finite-stack, finite-alphabet Turing machine with a polynomial step bound.

Mathlib's `FinTM2` only supplies alphabet finiteness for the input stack.  The
extra condition here requires *every* stack alphabet to be finite.  Thus one
cannot store an arbitrary natural number or a function in a single stack symbol.
-/
def Polytime {α β : Type} (ea : α → BitString) (eb : β → BitString)
    (f : α → β) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime ea eb f, ∀ k, Finite (M.tm.Γ k)

/-! ## 3CNF formulas -/

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

structure Clause where
  first : Literal
  second : Literal
  third : Literal
  deriving DecidableEq

/-- Exactly three literals per clause; repetitions are permitted. -/
abbrev Formula := List Clause

def Literal.eval (v : ℕ → Bool) (l : Literal) : Bool :=
  if l.positive then v l.index else !(v l.index)

def Clause.eval (v : ℕ → Bool) (c : Clause) : Bool :=
  c.first.eval v || c.second.eval v || c.third.eval v

def Satisfiable (F : Formula) : Prop :=
  ∃ v : ℕ → Bool, ∀ c ∈ F, c.eval v = true

def Literal.encode (l : Literal) : BitString := l.positive :: encodeNat l.index

def Clause.encode (c : Clause) : BitString :=
  c.first.encode ++ c.second.encode ++ c.third.encode

def encodeFormula (F : Formula) : BitString :=
  encodeNat F.length ++ F.flatMap Clause.encode

def formulaSize (F : Formula) : ℕ := (encodeFormula F).length

def encodeGraph (G : Graph) : BitString :=
  encodeNat G.n ++ (List.finRange G.n).flatMap (fun i =>
    (List.finRange G.n).flatMap (fun j => encodeRat (G.capacity i j)))

/-- The rational threshold is additional to the graph. -/
structure Instance where
  graph : Graph
  threshold : ℚ
  threshold_pos : 0 < threshold

def encodeInstance (I : Instance) : BitString :=
  block (encodeGraph I.graph) ++ encodeRat I.threshold

/-- This records graph size, every numeric bit length, and total output length.
The polynomial is quantified *inside* the choice of the fixed factor. -/
def OutputBound (R : Formula → Instance) (p : Polynomial ℕ) : Prop :=
  ∀ F, let I := R F
    I.graph.n + I.graph.n ^ 2 ≤ p.eval (formulaSize F) ∧
    (∀ i j, (encodeRat (I.graph.capacity i j)).length ≤ p.eval (formulaSize F)) ∧
    (encodeRat I.threshold).length ≤ p.eval (formulaSize F) ∧
    (encodeInstance I).length ≤ p.eval (formulaSize F)

/-- Polynomial-time gap reduction for the specific objective above. -/
def HasGapReduction (C : ℝ) : Prop :=
  ∃ R : Formula → Instance,
    Polytime encodeFormula encodeInstance R ∧
    (∃ p : Polynomial ℕ, OutputBound R p) ∧
    (∀ F, Satisfiable F → (R F).graph.phi ≤ (R F).threshold) ∧
    (∀ F, ¬ Satisfiable F → C * ((R F).threshold : ℝ) < ((R F).graph.phi : ℝ))

/-! ## The approximation search problem and NP-hardness -/

/-- A cut is returned as one bit per vertex, in vertex order. -/
def cutOfBits (G : Graph) (s : BitString) : Finset (Fin G.n) :=
  Finset.univ.filter (fun i => s[i.val]?.getD false = true)

/-- The approximation algorithm must return a feasible cut, not just an estimated value. -/
def ApproxAnswer (C : ℝ) (G : Graph) (s : BitString) : Prop :=
  s.length = G.n ∧ IsCut (cutOfBits G s) ∧
    (G.cutRatio (cutOfBits G s) : ℝ) ≤ C * (G.phi : ℝ)

abbrev Language := BitString → Prop

/-- NP via a deterministic polynomial-time verifier and a polynomial-length certificate. -/
def InNP (L : Language) : Prop :=
  ∃ (V : BitString × BitString → Bool) (p : Polynomial ℕ),
    Polytime encodePair encodeBool V ∧
    ∀ x, L x ↔ ∃ w, w.length ≤ p.eval x.length ∧ V (x, w) = true

/-- NP-hardness of the factor-`C` search problem, under one-call polynomial-time
oracle reductions.  The postprocessor must work for *every* valid approximate
answer, not just for a helpful choice of answer. -/
def ApproximationNPHard (C : ℝ) : Prop :=
  ∀ L : Language, InNP L →
    ∃ (query : BitString → Graph) (decideAnswer : BitString × BitString → Bool),
      Polytime id encodeGraph query ∧
      Polytime encodePair encodeBool decideAnswer ∧
      ∀ x s, ApproxAnswer C (query x) s → (decideAnswer (x, s) = true ↔ L x)

def bitsOfCut (G : Graph) (S : Finset (Fin G.n)) : BitString :=
  List.ofFn (fun i : Fin G.n => decide (i ∈ S))

@[simp] theorem bitsOfCut_length (G : Graph) (S : Finset (Fin G.n)) :
    (bitsOfCut G S).length = G.n := by simp [bitsOfCut]

@[simp] theorem cutOfBits_bitsOfCut (G : Graph) (S : Finset (Fin G.n)) :
    cutOfBits G (bitsOfCut G S) = S := by
  ext i
  simp [cutOfBits, bitsOfCut]

/-- Every graph has a factor-`C` approximation when `C ≥ 1`. -/
theorem exists_approximation_answer (G : Graph) {C : ℝ} (hC : 1 ≤ C) :
    ∃ s, ApproxAnswer C G s := by
  obtain ⟨S, hS, hmin⟩ := G.exists_minimizing_cut
  refine ⟨bitsOfCut G S, bitsOfCut_length G S, ?_, ?_⟩
  · simpa using hS
  · rw [cutOfBits_bitsOfCut, hmin]
    have hp : (0 : ℝ) ≤ G.phi := by exact_mod_cast G.phi_nonneg
    simpa using mul_le_mul_of_nonneg_right hC hp

/-- Rational comparison of the returned cut with a fixed rational factor `B`.
No real-number oracle is used by this predicate. -/
def decideGap (B : ℚ) (I : Instance) (s : BitString) : Bool :=
  decide (I.graph.cutRatio (cutOfBits I.graph s) ≤ B * I.threshold)

/-- A gap for a larger rational factor decides satisfiability from every valid
approximation at the target real factor. -/
theorem gap_decision_correct {F : Formula} {I : Instance} {C : ℝ} {B : ℚ}
    (hC : 0 ≤ C) (hCB : C ≤ (B : ℝ))
    (hyes : Satisfiable F → I.graph.phi ≤ I.threshold)
    (hno : ¬ Satisfiable F → (B : ℝ) * I.threshold < I.graph.phi)
    {s : BitString} (hs : ApproxAnswer C I.graph s) :
    decideGap B I s = true ↔ Satisfiable F := by
  simp only [decideGap, decide_eq_true_eq]
  constructor
  · intro hratio
    by_contra hunsat
    have hno' := hno hunsat
    have hp : (I.graph.phi : ℝ) ≤ I.graph.cutRatio (cutOfBits I.graph s) := by
      exact_mod_cast I.graph.phi_le_cutRatio hs.2.1
    have hr : (I.graph.cutRatio (cutOfBits I.graph s) : ℝ) ≤ (B : ℝ) * I.threshold := by
      exact_mod_cast hratio
    linarith only [hno', hp, hr]
  · intro hsat
    have hp : (I.graph.phi : ℝ) ≤ I.threshold := by exact_mod_cast hyes hsat
    have ha : (0 : ℝ) ≤ I.threshold := by exact_mod_cast I.threshold_pos.le
    have hbound := hs.2.2.trans (mul_le_mul_of_nonneg_left hp hC)
    have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hCB ha)
    exact_mod_cast hbound'

end UniformSparsestCut

end OAI
