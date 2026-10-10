import OAI.NumberTheory.Jacobsthal.Estimates.NestedDegreeBounds
import OAI.NumberTheory.Jacobsthal.Estimates.NestedPartials

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

theorem irreducible_of_constant_polynomial (p : Polynomial ℂ)
    (hp : Irreducible (Polynomial.C p : Nested ℂ)) : Irreducible p := by
  refine ⟨fun h => hp.not_isUnit (Polynomial.isUnit_C.mpr h), ?_⟩
  intro a b hab
  have h := hp.2 (show Polynomial.C p = Polynomial.C a*Polynomial.C b by rw [hab, map_mul])
  exact h.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp

theorem nonlinear_outer_degree_pos (E : MV ℂ ≃ₐ[ℂ] Nested ℂ) (i : Fin 2)
    (hXi : E (MvPolynomial.X i) = Polynomial.C Polynomial.X)
    (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) : 0 < (E Q).natDegree := by
  have hC (c : ℂ) : E (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
    simpa using E.commutes c
  have hEQ : Irreducible (E Q) := (MulEquiv.irreducible_iff E.toMulEquiv).mpr hQ
  by_contra! hzero
  have he : E Q = Polynomial.C ((E Q).coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hzero
  have hc : Irreducible ((E Q).coeff 0) := irreducible_of_constant_polynomial _ (he ▸ hEQ)
  have hlin := Polynomial.eq_X_add_C_of_degree_le_one
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ hc).le
  let a : ℂ := ((E Q).coeff 0).coeff 1
  let b : ℂ := ((E Q).coeff 0).coeff 0
  have hQlin : Q = MvPolynomial.C a*MvPolynomial.X i+MvPolynomial.C b := by
    apply E.injective
    rw [map_add, map_mul, hC, hC, hXi, he, hlin]
    simp only [map_add, map_mul, a, b]
  have ht : Q.totalDegree ≤ 1 := by
    rw [hQlin]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp
  omega

theorem nonlinear_nestedX_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedX ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedX ℂ) 1 (nestedX_X_one ℂ) Q hQ hdeg

theorem nonlinear_nestedY_degree_pos (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    0 < (nestedY ℂ Q).natDegree :=
  nonlinear_outer_degree_pos (nestedY ℂ) 0 (nestedY_X_zero ℂ) Q hQ hdeg

theorem nonlinear_partial_zero_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 0 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedX ℂ) hz
  rw [nestedX_partial_zero, map_zero] at hd
  exact (nonlinear_nestedX_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_one_ne (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree) :
    MvPolynomial.pderiv 1 Q ≠ 0 := by
  intro hz
  have hd := congrArg (nestedY ℂ) hz
  rw [nestedY_partial_one, map_zero] at hd
  exact (nonlinear_nestedY_degree_pos Q hQ hdeg).ne' (Polynomial.derivative_eq_zero.mp hd)

theorem nonlinear_partial_not_dvd (Q : MV ℂ) (hQ : Irreducible Q) (hdeg : 1 < Q.totalDegree)
    (i : Fin 2) : ¬ Q ∣ MvPolynomial.pderiv i Q := by
  have hn : MvPolynomial.pderiv i Q ≠ 0 := by
    fin_cases i
    · exact nonlinear_partial_zero_ne Q hQ hdeg
    · exact nonlinear_partial_one_ne Q hQ hdeg
  intro hd
  have h1 := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd hn
  have h2 := partial_totalDegree_le ℂ Q i
  omega

end ErdosCriticalGeometry

end

end Erdos970

end OAI
