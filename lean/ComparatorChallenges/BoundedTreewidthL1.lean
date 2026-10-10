import Mathlib

namespace OAI

noncomputable section

namespace BoundedTreewidthL1

universe u_1

variable {V : Type u_1} (G : SimpleGraph V)

/-- Sum of the given positive real edge lengths along a graph walk. -/
def walkLength (ℓ : G.edgeSet → ℝ) : {u v : V} → G.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) h p => ℓ ⟨s(u, v), h⟩ + walkLength ℓ p

noncomputable def shortestPathDistance (ℓ : G.edgeSet → ℝ) (u v : V) : ℝ :=
  sInf {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}

def HasTreeDecomposition [DecidableEq V] (k : ℕ) : Prop :=
  ∃ n : ℕ, ∃ T : SimpleGraph (Fin n), ∃ bag : Fin n → Finset V,
    T.IsTree ∧
    (∀ v : V, ∃ t, v ∈ bag t) ∧
    (∀ u v : V, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
    (∀ v : V, (T.induce {t | v ∈ bag t}).Connected) ∧
    (∀ t, (bag t).card ≤ k)

/-- A map to genuine finite-dimensional real ℓ₁, not just a cut pseudometric. -/
def HasL1Embedding (ℓ : G.edgeSet → ℝ) (C : ℝ) : Prop :=
  ∃ m : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
    ∀ u v : V,
      shortestPathDistance G ℓ u v ≤ ‖F u - F v‖ ∧
      ‖F u - F v‖ ≤ C * shortestPathDistance G ℓ u v

def MainStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V),
      G.Connected → HasTreeDecomposition G k →
      ∀ ℓ : G.edgeSet → ℝ, (∀ e, 0 < ℓ e) → HasL1Embedding G ℓ C

theorem main_theorem : MainStatement := by
  sorry

end BoundedTreewidthL1

end

end OAI
