import Mathlib

namespace OAI

/-! The finite-graph Ramsey number and its asymptotic bounds. -/

namespace SharpLogRamsey

def RamseyProperty (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ A : Finset (Fin N), G.IsNClique s A) ∨
    (∃ B : Finset (Fin N), Gᶜ.IsNClique t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {N | RamseyProperty s t N}

def MainBounds (s : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (t : ℝ) ^ (s - 1) / Real.rpow (Real.log (t : ℝ)) ((s - 2 : ℕ) + ε)
        ≤ (ramsey s t : ℝ) ∧
      (ramsey s t : ℝ) ≤ C * (t : ℝ) ^ (s - 1) /
        (Real.log (t : ℝ)) ^ (s - 2)

def MainLimit (s : ℕ) : Prop :=
  Filter.Tendsto
    (fun t : ℕ =>
      (((s - 1 : ℕ) : ℝ) * Real.log (t : ℝ) - Real.log (ramsey s t : ℝ)) /
        Real.log (Real.log (t : ℝ)))
    Filter.atTop (nhds ((s - 2 : ℕ) : ℝ))

end SharpLogRamsey

end OAI
