import Mathlib

namespace OAI

section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I

end MetricKMedian
end
end

namespace MetricKMedian
namespace Complexity
/-- Polynomial-time computation with every physical work alphabet finite. -/
def FinitePolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ p : Turing.TM2ComputableInPolyTime ea eb f,
    ∀ k : p.tm.K, Finite (p.tm.Γ k)

abbrev Word := List Bool
abbrev Language := Set Word

def encodeBit (b : Bool) : Word := [b]

def encodePair (x : Word × Word) : Word :=
  encodeNat x.1.length ++ x.1 ++ x.2

def P : Set Language := {L | ∃ decideL : Word → Bool,
  FinitePolyTime id encodeBit decideL ∧ ∀ x, decideL x = true ↔ x ∈ L}

def NP : Set Language := {L | ∃ (verify : Word × Word → Bool) (p : Polynomial ℕ),
  FinitePolyTime encodePair encodeBit verify ∧
  ∀ x, x ∈ L ↔ ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x, w) = true}

/-- Separation of deterministic polynomial time from finite-verifier nondeterministic polynomial time. -/
def PNeNP : Prop := P ≠ NP

end Complexity
/-- An actual nonempty feasible facility set, encoded by its membership mask. -/
def FactorCorrect (α : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ α * optimum I

/-- Deterministic polynomial-time approximation factors for arbitrary specified clients and facilities. -/
def approximationFactors : Set ℝ := {α | ∃ algorithm : Instance → List Bool,
  Complexity.FinitePolyTime encodeInstance id algorithm ∧
  ∀ I, FactorCorrect α I (algorithm I)}

end MetricKMedian

namespace MetricKMedian
/-- The deterministic approximation threshold is an infimum; its attainment is not asserted. -/
theorem threshold (h : Complexity.PNeNP) :
    sInf approximationFactors=1+2/Real.exp 1 := by
  sorry
end MetricKMedian

end OAI
