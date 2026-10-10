import Mathlib

namespace OAI

/-!
Finite signed words, computable word problem, simple embeddings, and action-envelope predicates.
-/

namespace FiniteAlgebraicEnvelopes

universe u

/-- Finite signed words, with `true` denoting a generator and `false` its inverse. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- Evaluation in the specified finite generating family. -/
def evalWord {G : Type u} [Group G] {n : ℕ} (s : Fin n → G) (w : Word n) : G :=
  (w.map fun a => if a.2 then s a.1 else (s a.1)⁻¹).prod

/-- Algorithmic decidability, not merely classical `DecidablePred`. -/
def HasDecidableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (s : Fin n → G),
    Subgroup.closure (Set.range s) = ⊤ ∧
    ComputablePred (fun w : Word n => evalWord s w = 1)

/-- The nontriviality in `IsSimpleGroup` is part of Mathlib's definition. -/
def EmbedsInFinitelyPresentedSimpleGroup (G : Type u) [Group G] : Prop :=
  ∃ (H : Type u) (_ : Group H),
    Group.IsFinitelyPresented H ∧ IsSimpleGroup H ∧
    ∃ f : G →* H, Function.Injective f

/-- Action-envelope hypotheses. -/
def HasActionEnvelope (G : Type u) [Group G] : Prop :=
  ∃ (Γ : Type u) (_ : Group Γ) (X : Type u) (_ : MulAction Γ X),
    Group.IsFinitelyPresented Γ ∧ Countable X ∧ Infinite X ∧
    FaithfulSMul Γ X ∧
    (∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂) ∧
    (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
    ∃ f : G →* Γ, Function.Injective f

end FiniteAlgebraicEnvelopes

end OAI
