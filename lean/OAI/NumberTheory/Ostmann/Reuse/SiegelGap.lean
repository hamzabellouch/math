import OAI.NumberTheory.Jacobsthal.Siegel.DirichletRealZeroBoundProof
import OAI.NumberTheory.Ostmann.Reuse.SiegelNearOne

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

namespace Ostmann.Dirichlet

theorem exists_uniform_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) :=
  Erdos970.WeightedTorusJets.dirichletRealZeroBound_proof

end Ostmann.Dirichlet

end OAI
