import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.HilbertSeries
import OAI.NumberTheory.SiegelZeros.Structure.ConeMapEval

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finrank_degreePiece_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K)) (hprime : I.IsPrime)
    {i : σ} (hi : X i ∉ I) (n : ℕ) :
    0 < Module.finrank K (degreePiece I n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨Ideal.Quotient.mk I (X i ^ n), X i ^ n, isHomogeneous_X_pow i n, rfl⟩, ?_⟩
  intro hzero
  exact hi (hprime.mem_of_pow_mem n
    (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hzero)))

theorem hilbertPolynomial_ne_zero_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : hilbertPolynomial I hI ≠ 0 := by
  obtain ⟨i, hi⟩ := hvars
  obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
  intro hzero
  have h := hN (N + 1) (by omega)
  rw [hzero, Polynomial.eval_zero] at h
  have hpos := finrank_degreePiece_pos_of_prime_variable_not_mem I hprime hi (N + 1)
  exact (Nat.ne_of_gt hpos) (by exact_mod_cast h)

theorem projectiveDegree_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : 0 < projectiveDegree I hI :=
  (projectiveDegree_pos_iff I hI).mpr
    (hilbertPolynomial_ne_zero_of_prime_variable_not_mem I hI hprime hvars)

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
open MvPolynomial

theorem cone_projectiveDegree_pos
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    0 < projectiveDegree (coneIdeal p) (coneIdeal_isHomogeneous p) :=
  projectiveDegree_pos_of_prime_variable_not_mem
    (coneIdeal p) (coneIdeal_isHomogeneous p) (coneIdeal_isPrime p)
    ⟨none, X_none_not_mem_coneIdeal p⟩

end WeightedTorusJets.Geometry.GradedQuotient



end SiegelZeros

end OAI
