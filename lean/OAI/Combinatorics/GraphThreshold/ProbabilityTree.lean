import OAI.Combinatorics.GraphThreshold.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fintype.Sigma

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

/-- Equal-depth trees carrying an actual strictly positive child law at every branch. -/
inductive ProbabilityTree (X : Type) : ℕ → Type 1
  | leaf : ProbabilityTree X 0
  | node {d : ℕ} (B : Type) [Fintype B] (law : FiniteLaw B)
      (positive : law.IsPositive) (label : B → Finset X)
      (child : B → ProbabilityTree X d) : ProbabilityTree X (d + 1)

/-- A function inspects only the indicated coordinates of its input subset. -/
def DependsOnlyOn {X β : Type*} [DecidableEq X] (S : Finset X)
    (f : Finset X → β) : Prop :=
  ∀ W V, W ∩ S = V ∩ S → f W = f V

/-- A function is unchanged by modifications inside the indicated coordinates. -/
def DependsOutside {X β : Type*} [DecidableEq X] (A : Finset X)
    (f : Finset X → β) : Prop :=
  ∀ W V, W \ A = V \ A → f W = f V

namespace ProbabilityTree

variable {X : Type}

/-- Full root-to-leaf paths, retaining distinct child-index histories. -/
def Path : {d : ℕ} → ProbabilityTree X d → Type
  | _, .leaf => PUnit
  | _, @node _ _ B _ _ _ _ child => Σ b : B, Path (child b)

/-- The list of arc labels along a full path, in root-to-leaf order. -/
def pathLabels : {d : ℕ} → (T : ProbabilityTree X d) → T.Path → List (Finset X)
  | _, .leaf => fun _ => []
  | _, @node _ _ _B _ _ _ label child => fun p =>
      label p.1 :: pathLabels (child p.1) p.2

/-- Every path family is finite; no quotient by labels is taken. -/
instance pathFintype : {d : ℕ} → (T : ProbabilityTree X d) → Fintype T.Path
  | _, .leaf => inferInstanceAs (Fintype PUnit)
  | _, @node _ _ B _ _ _ _ child => by
      letI : ∀ b : B, Fintype (Path (child b)) := fun b => pathFintype (child b)
      exact inferInstanceAs (Fintype (Σ b : B, Path (child b)))

section Labels

variable [DecidableEq X]

/-- Union of all arc labels along a specified full path. -/
def pathUnion : {d : ℕ} → (T : ProbabilityTree X d) → T.Path → Finset X
  | _, .leaf => fun _ => ∅
  | _, @node _ _ _B _ _ _ label child => fun p =>
      label p.1 ∪ pathUnion (child p.1) p.2

/-- All coordinates used by any arc anywhere in the tree. -/
def support : {d : ℕ} → ProbabilityTree X d → Finset X
  | _, .leaf => ∅
  | _, @node _ _ B inst _ _ label child =>
      (@Finset.univ B inst).biUnion fun b => label b ∪ support (child b)

/-- A recursive form of disjointness, equivalent to pairwise disjoint labels on every full path. -/
def IsDisjoint : {d : ℕ} → ProbabilityTree X d → Prop
  | _, .leaf => True
  | _, @node _ _ _ _ _ _ label child =>
      (∀ b, Disjoint (label b) (support (child b))) ∧ ∀ b, IsDisjoint (child b)

/-- Literal pairwise disjointness along every full root-to-leaf path. -/
def PathDisjoint {d : ℕ} (T : ProbabilityTree X d) : Prop :=
  ∀ p : T.Path, (T.pathLabels p).Pairwise Disjoint

/-- Per-level spread conditions, starting with index zero at the root. -/
def HasSpread : {d : ℕ} → ProbabilityTree X d → (ℕ → ℝ) → Prop
  | _, .leaf, _ => True
  | _, @node _ _ _ _ law _ label child, a =>
      IsSpread law label (a 0) ∧ ∀ b, HasSpread (child b) (fun j => a (j + 1))

/-- The event that some full path is covered by a given set. -/
def CoveredBy {d : ℕ} (T : ProbabilityTree X d) (W : Finset X) : Prop :=
  ∃ p : T.Path, T.pathUnion p ⊆ W

end Labels

/-- Per-level cardinality capacities, starting with index zero at the root. -/
def HasCapacities : {d : ℕ} → ProbabilityTree X d → (ℕ → ℕ) → Prop
  | _, .leaf, _ => True
  | _, @node _ _ _ _ _ _ label child, m =>
      (∀ b, (label b).card ≤ m 0) ∧ ∀ b, HasCapacities (child b) (fun j => m (j + 1))

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI
