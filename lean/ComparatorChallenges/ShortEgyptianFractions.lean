import Mathlib

namespace OAI

namespace ShortEgyptian

def IsExpansion (a b : ℕ) (ns : List ℕ) : Prop :=
  ns.Pairwise (· < ·) ∧ (∀ n ∈ ns, 2 ≤ n) ∧
    (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = (a : ℚ) / (b : ℚ)

noncomputable def minLength (a b : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}

noncomputable def maxMinLength (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a => minLength a b)

theorem main :
    (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ)) := by
  sorry

end ShortEgyptian

end OAI
