import OAI.Analysis.Laughlin.Spin.Polynomial2

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem monomialExponent_degree {N Q : ℕ} (a : Configuration N Q) :
    (monomialExponent a).degree = N * Q := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  have h (i : Fin N) : ∑ b : Bool, monomialExponent a (i,b) = Q := by
    simpa [monomialExponent, Nat.add_comm] using Nat.sub_add_cancel (Nat.le_of_lt_succ (a i).isLt)
  simp_rw [h]
  simp

theorem spinPolynomial_isHomogeneous {N Q : ℕ} (ψ : State N Q) :
    (spinPolynomial ψ).IsHomogeneous (N * Q) := by
  apply IsHomogeneous.sum
  intro a ha
  exact isHomogeneous_monomial _ (monomialExponent_degree a)

theorem spinPolynomial_totalDegree_le {N Q : ℕ} (ψ : State N Q) :
    (spinPolynomial ψ).totalDegree ≤ N * Q :=
  (spinPolynomial_isHomogeneous ψ).totalDegree_le

theorem state_eq_laughlin_of_pair_cubes {N : ℕ} (ψ : State N (3*(N-1)))
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ spinPolynomial ψ) :
    ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  obtain ⟨c,hc⟩ := scalar_laughlin_at_flux (spinPolynomial ψ)
    (spinPolynomial_totalDegree_le ψ) hcubes
  exact ⟨c,state_eq_laughlin_of_polynomial ψ c hc⟩

end Laughlin

end OAI
