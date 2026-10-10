import OAI.Combinatorics.Progressions.Polynomial.RealPolarizedPolynomialOrbit

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizedCoefficient_self (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι)
    (ha : a.val ≠ 0) :
    squarefreePolynomialEquiv (F.polarizedCoefficient π p a).val a =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        coefficients p.val (blockExponent π a.val) := by
  rw [F.polarizedCoefficient_coe π p a ha, map_smul, Pi.smul_apply,
    squarefreePolynomialEquiv_monomial_self]

theorem polarizedCoefficient_ne (p : F.adaptedLieSubalgebra) (a c : SquarefreeIndex ι)
    (hac : a ≠ c) : squarefreePolynomialEquiv (F.polarizedCoefficient π p a).val c = 0 := by
  by_cases ha : a.val = 0
  · rw [F.polarizedCoefficient_zero π p a ha]
    exact congrFun (map_zero squarefreePolynomialEquiv) c
  · rw [F.polarizedCoefficient_coe π p a ha, map_smul, Pi.smul_apply,
      squarefreePolynomialEquiv_monomial_ne a c hac, smul_zero]

theorem polarizedLog_eval_coefficient (p : F.adaptedLieSubalgebra)
    (x : ι → ℚ) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (eval x (F.polarizedLog π p)).val c =
      (c.val.prod fun i n => x i ^ n) •
        squarefreePolynomialEquiv (F.polarizedCoefficient π p c).val c := by
  classical
  let C : F.SquarefreeAlgebra π →ₗ[ℚ] L := (LinearMap.proj c).comp
    (squarefreePolynomialEquiv.toLinearMap.comp (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap)
  change C (eval x (F.polarizedLog π p)) = _
  rw [F.polarizedLog_eval, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single c]
  · rfl
  · intro a _ hac
    have hz : C (F.polarizedCoefficient π p a) = 0 := F.polarizedCoefficient_ne π p a c hac
    rw [hz, smul_zero]
  · simp

end Erdos3.MultidegreeLieFiltration

end

end OAI
