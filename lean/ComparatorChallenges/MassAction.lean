import Mathlib

namespace OAI

noncomputable section

namespace Problem326

structure ReactionNetwork (d : ℕ) where
  complexes : Finset (Fin d → ℕ)
  reactions : Finset ((Fin d → ℕ) × (Fin d → ℕ))
  source_mem : ∀ e ∈ reactions, e.1 ∈ complexes
  target_mem : ∀ e ∈ reactions, e.2 ∈ complexes
  source_ne_target : ∀ e ∈ reactions, e.1 ≠ e.2

abbrev Reaction {d : ℕ} (N : ReactionNetwork d) :=
  {e : (Fin d → ℕ) × (Fin d → ℕ) // e ∈ N.reactions}

def HasReaction {d : ℕ} (N : ReactionNetwork d)
    (y z : Fin d → ℕ) : Prop :=
  (y, z) ∈ N.reactions

def WeaklyReversible {d : ℕ} (N : ReactionNetwork d) : Prop :=
  ∀ e : Reaction N,
    Relation.TransGen (HasReaction N) e.val.2 e.val.1

def monomial {d : ℕ} (x : Fin d → ℝ) (y : Fin d → ℕ) : ℝ :=
  Finset.univ.prod (fun i => x i ^ y i)

def massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Finset.univ.sum (fun e : Reaction N =>
    κ e * monomial x e.val.1 *
      ((e.val.2 i : ℝ) - (e.val.1 i : ℝ)))

def PositiveState {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ i, 0 < x i

def IsGlobalForwardSolution {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x0 : Fin d → ℝ)
    (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt x (massAction N κ (x t)) t

theorem global_bounded_persistent_solution :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  sorry

end Problem326

end

end OAI
