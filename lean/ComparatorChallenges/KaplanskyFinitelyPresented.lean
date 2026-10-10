import Mathlib

namespace OAI.KaplanskyCounterexample

/-- A finite characteristic-two field and a finitely presented group with odd-prime
order torsion give a counterexample to direct finiteness (paper, Theorem 1.1). -/
theorem finitelyPresented_counterexample :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1 := by
  sorry

end OAI.KaplanskyCounterexample
