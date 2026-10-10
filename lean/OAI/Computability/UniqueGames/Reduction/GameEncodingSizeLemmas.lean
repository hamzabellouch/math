import Std
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI

section

/-!
Bit-length bounds for the concrete unique-game serialization. Every stored
constraint occurrence and every entry of its forward permutation table is
encoded. These are output-size bounds, not machine running-time bounds.
-/

namespace UniqueGamesTheorem.Reduction.GameEncodingSize

open Foundations.Target Foundations.Complexity

/-- The full table has `q` labels, each with unary encoding length at most `q+1`.
The conservative bound remains valid when the alphabet is empty. -/
theorem tableBits_length_le {q : Nat} (table : PermutationTable q) :
    (encodeWords (tableWords table)).length ≤ q * (q + 1) := by
  have h := encodeWords_length_le (tableWords table) q (by
    intro value hvalue
    obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hvalue
    rw [← hlabel]
    exact Nat.le_of_lt label.isLt)
  simpa only [tableWords_length] using h

/-- Both endpoint words use at most `n` bits, and the entire forward table is
retained. A constraint itself supplies the endpoint bounds, even for small `n`. -/
theorem constraintBits_length_le {n q : Nat} (constraint : Constraint n q) :
    (encodeWords (constraintWords constraint)).length ≤ 2 * n + q * (q + 1) := by
  have hs := constraint.source.isLt
  have ht := constraint.target.isLt
  have hp := tableBits_length_le constraint.permutation
  simp only [constraintWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

/-- Each occurrence contributes its own complete encoding; no deduplication
or implicit edge weights enter the bound. The empty list is also covered. -/
theorem constraintsBits_length_le {n q : Nat} (constraints : List (Constraint n q)) :
    (encodeWords (constraints.flatMap constraintWords)).length ≤
      constraints.length * (2 * n + q * (q + 1)) := by
  induction constraints with
  | nil => simp [encodeWords]
  | cons constraint constraints ih =>
      have hc := constraintBits_length_le constraint
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Exact header accounting plus a bound on every serialized occurrence.
No lower bound on the alphabet or vertex count is assumed. -/
theorem gameBits_length_le {q : Nat} (g : Instance q) :
    (gameBits g).length ≤
      g.vertices + q + g.constraints.length + 3 +
        g.constraints.length * (2 * g.vertices + q * (q + 1)) := by
  have h := constraintsBits_length_le g.constraints
  simp only [gameBits, gameWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Reduction.GameEncodingSize

end

section

namespace UniqueGamesTheorem.Reduction.Incidence

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

def parity (a : Triple) : Bool := (a.first.xor a.second).xor a.third

def matchingSlots (a b : Triple) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

/-- Invalid Alice answers lose in every slot. -/
def acceptedSlots (a b : Triple) (rhs : Bool) : Nat :=
  if parity a = rhs then matchingSlots a b else 0

def failedEquation (b : Triple) (rhs : Bool) : Nat :=
  if parity b = rhs then 0 else 1

/-- Copy a satisfying Bob triple; otherwise flip its first bit. -/
def bestResponse (b : Triple) (rhs : Bool) : Triple :=
  if parity b = rhs then b else { b with first := !b.first }

theorem local_count_bound (a b : Triple) (rhs : Bool) :
    acceptedSlots a b rhs + failedEquation b rhs ≤ 3 := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

theorem best_response_exact (b : Triple) (rhs : Bool) :
    acceptedSlots (bestResponse b rhs) b rhs + failedEquation b rhs = 3 := by
  rcases b with ⟨b₁, b₂, b₃⟩
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

universe variableUniverse indexUniverse

structure Equation (Variable : Type variableUniverse) where
  first : Variable
  second : Variable
  third : Variable
  rhs : Bool

variable {Variable : Type variableUniverse} {Index : Type indexUniverse}

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def nameAt (e : Equation Variable) : Slot → Variable
  | .first => e.first
  | .second => e.second
  | .third => e.third

def bitAt (a : Triple) : Slot → Bool
  | .first => a.first
  | .second => a.second
  | .third => a.third

/-- A predicate of the actual questions and answers, with no hidden slot input. -/
def questionPredicate (e : Equation Variable) (name : Variable)
    (alice : Triple) (bob : Bool) : Prop :=
  parity alice = e.rhs ∧
    ((e.first = name ∧ alice.first = bob) ∨
     (e.second = name ∧ alice.second = bob) ∨
     (e.third = name ∧ alice.third = bob))

/-- Cloning supplies exactly the distinctness needed to recover a slot from its name. -/
theorem question_predicate_at_slot (e : Equation Variable)
    (distinct₁₂ : e.first ≠ e.second) (distinct₁₃ : e.first ≠ e.third)
    (distinct₂₃ : e.second ≠ e.third) (alice : Triple) (bob : Bool) (slot : Slot) :
    questionPredicate e (nameAt e slot) alice bob ↔
      parity alice = e.rhs ∧ bitAt alice slot = bob := by
  cases slot <;>
    simp [questionPredicate, nameAt, bitAt, distinct₁₂, distinct₁₃, distinct₂₃,
      Ne.symm distinct₁₂, Ne.symm distinct₁₃, Ne.symm distinct₂₃]

/-- Bob receives only a variable name: the strategy has no occurrence input. -/
def bobTriple (g : Variable → Bool) (e : Equation Variable) : Triple :=
  ⟨g e.first, g e.second, g e.third⟩

/-- An occurrence index supplies Alice's full question and its equation. -/
def acceptedCount (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) : List Index → Nat
  | [] => 0
  | i :: rest =>
    acceptedSlots (alice i) (bobTriple g (equations i)) (equations i).rhs +
      acceptedCount equations g alice rest

def failureCount (equations : Index → Equation Variable)
    (g : Variable → Bool) : List Index → Nat
  | [] => 0
  | i :: rest =>
    failedEquation (bobTriple g (equations i)) (equations i).rhs +
      failureCount equations g rest

theorem total_count_bound (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index) :
    acceptedCount equations g alice occurrences + failureCount equations g occurrences ≤
      3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := local_count_bound (alice i) (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons]
    omega

def optimalAlice (equations : Index → Equation Variable) (g : Variable → Bool)
    (i : Index) : Triple :=
  bestResponse (bobTriple g (equations i)) (equations i).rhs

theorem optimal_alice_exact (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    acceptedCount equations g (optimalAlice equations g) occurrences +
      failureCount equations g occurrences = 3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := best_response_exact (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons, optimalAlice]
    omega

/-- Exact finite-count form of `max_Alice Pr[accept | Bob = g] = 1 - u(g)/3`. -/
theorem fixed_bob_optimum (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    ∃ alice : Index → Triple,
      acceptedCount equations g alice occurrences + failureCount equations g occurrences =
        3 * occurrences.length ∧
      ∀ other : Index → Triple,
        acceptedCount equations g other occurrences ≤
          acceptedCount equations g alice occurrences := by
  refine ⟨optimalAlice equations g, optimal_alice_exact equations g occurrences, ?_⟩
  intro other
  have h := total_count_bound equations g other occurrences
  have heq := optimal_alice_exact equations g occurrences
  omega

theorem soundness_191_over_192 (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index)
    (source_gap : occurrences.length ≤ 64 * failureCount equations g occurrences) :
    64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  have h := total_count_bound equations g alice occurrences
  omega

/-- The same bound holds for every deterministic pair when every Bob assignment has the gap. -/
theorem game_soundness_191_over_192 (equations : Index → Equation Variable)
    (occurrences : List Index)
    (source_gap : ∀ g : Variable → Bool,
      occurrences.length ≤ 64 * failureCount equations g occurrences) :
    ∀ (g : Variable → Bool) (alice : Index → Triple),
      64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  intro g alice
  exact soundness_191_over_192 equations g alice occurrences (source_gap g)

end UniqueGamesTheorem.Reduction.Incidence

end

end OAI
