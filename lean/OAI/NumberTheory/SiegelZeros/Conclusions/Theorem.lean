import OAI.NumberTheory.SiegelZeros.Intersection.BezoutBoundary

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets

theorem exists_absolute_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  exact SiegelZerosAwei.W50.uniform_exclusion_of_local_isolated_bezout
    (W22.localIsolatedBezout_of_actual_regular_selection ℂ)

end WeightedTorusJets

end

end SiegelZeros

end OAI
