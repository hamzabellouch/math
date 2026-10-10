import Mathlib
import OAI.Combinatorics.IndependentSets.Model

namespace OAI

namespace LargeIndependentSets

structure GraphReduction (δ : ℚ) where
  reduce : List Bool → Graph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) graphBits reduce
  finiteAlphabets : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)
  outputBound : Polynomial ℕ
  outputSize : ∀ b, (graphBits (reduce b)).length ≤ outputBound.eval b.length
  completeness : ∀ φ : Formula, φ.Satisfiable → (reduce (formulaBits φ)).ThreeColorable
  soundness : ∀ φ : Formula, ¬φ.Satisfiable →
    ((reduce (formulaBits φ)).independenceNumber : ℚ) <
      δ * (reduce (formulaBits φ)).vertices

def MainStatement : Prop :=
  ∀ δ : ℚ, 0 < δ → δ < 1 / 3 → Nonempty (GraphReduction δ)

end LargeIndependentSets

end OAI
