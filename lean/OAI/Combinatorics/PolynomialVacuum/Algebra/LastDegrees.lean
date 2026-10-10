import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedDegrees

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem interpolateState_last_degrees {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) :
    (interpolateState ψ χ s).degreeOf (Fin.last (n+1))≤n+1 ∧
    (s (Fin.last (n+1))=Spin.plus → (interpolateState ψ χ s).degreeOf (Fin.last (n+1))≤n) := by
  rw [interpolateState_eq_reinsert]
  constructor
  · exact (reinsertLast_degree _).trans (lastPolynomial_natDegree ψ χ s)
  · intro hs
    simp only [lastPolynomial,ite_eq_left hs]
    exact (reinsertLast_degree _).trans (canonicalInterpolant_natDegree _)

end PolynomialVacuumAlgebra

end OAI
