import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.InvariantJetMonomial

namespace OAI

namespace SiegelZeros

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem eval_one_invariantJet_monomial (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : ι →₀ ℕ) (r : R) :
    MvPolynomial.eval (fun _ => 1) (invariantJet c a (MvPolynomial.monomial m r)) =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) * r := by
  rw [invariantJet_monomial, MvPolynomial.smul_eval, MvPolynomial.eval_monomial]
  simp

end WeightedTorusJets.Geometry


end SiegelZeros

end OAI
