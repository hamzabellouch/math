import Mathlib

namespace OAI

namespace SiegelZeros
namespace WeightedTorusJets

def UniformSiegelZeroExclusion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q], 3 ≤ q →
    ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
        c ≤ (1 - β) * Real.log (q : ℝ)

end WeightedTorusJets
end SiegelZeros

end OAI
