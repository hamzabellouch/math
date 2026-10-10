import Mathlib
import PrimeNumberTheoremAnd.Erdos970.HadamardSupport
import OAI.NumberTheory.Jacobsthal.Siegel.DirichletRealZeroBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

end WeightedTorusJets

end

section
theorem WeightedTorusJets.dirichletRealZeroBound_proof :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  exact WeightedTorusJets.dirichlet_real_zero_bound

end

end Erdos970

end OAI
