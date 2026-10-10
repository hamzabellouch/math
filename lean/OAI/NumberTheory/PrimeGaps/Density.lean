import Mathlib

namespace OAI

noncomputable section

namespace Problem344

def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

def initialCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

def lowerAsymptoticDensity (A : Set ℕ) : ℝ :=
  sSup {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    d ≤ (initialCount A N : ℝ) / (N : ℝ)}

def largeGapIndices (C : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧
    C * Real.log (primeAt n : ℝ) <
      (primeAt (n + 1) : ℝ) - (primeAt n : ℝ)}

def ratioIncreaseIndices : Set ℕ :=
  {n | 1 ≤ n ∧
    (primeAt n : ℝ) / (n : ℝ) <
      (primeAt (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)}

end Problem344

end

end OAI
