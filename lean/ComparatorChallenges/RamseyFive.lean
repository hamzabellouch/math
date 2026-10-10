import Mathlib

namespace OAI

namespace SharpRamseyFive

def RamseyProperty (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique s A) ∨
    (∃ B : Finset (Fin n), G.IsNIndepSet t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {n : ℕ | RamseyProperty s t n}

def SharpBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    (t : ℝ) ^ 4 / Real.rpow (Real.log t) (3 + ε) ≤ (ramsey 5 t : ℝ) ∧
    (ramsey 5 t : ℝ) ≤ C * (t : ℝ) ^ 4 / (Real.log t) ^ 3

def SharpExponent : Prop :=
  Filter.Tendsto
    (fun t : ℕ => (4 * Real.log (t : ℝ) - Real.log (ramsey 5 t : ℝ)) /
      Real.log (Real.log (t : ℝ)))
    Filter.atTop (nhds (3 : ℝ))

theorem main : SharpBounds ∧ SharpExponent := by
  sorry

end SharpRamseyFive

end OAI
