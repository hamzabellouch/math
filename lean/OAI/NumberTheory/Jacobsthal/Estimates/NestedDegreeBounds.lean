import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem unique_degree_le_totalDegree (P : MvPolynomial (Fin 1) R) :
    (MvPolynomial.uniqueAlgEquiv R (Fin 1) P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hc
  have h := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  simp only [Finsupp.sum_single_index] at h
  exact (not_le_of_gt hk) h

theorem nestedX_degree_le (Q : MV R) : (nestedX R Q).natDegree ≤ Q.totalDegree := by
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).natDegree ≤ _
  exact Polynomial.natDegree_map_le.trans
    ((MvPolynomial.natDegree_finSuccEquiv Q).le.trans (MvPolynomial.degreeOf_le_totalDegree Q 0))

theorem nestedX_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedX R Q).coeff k).natDegree ≤ Q.totalDegree := by
  change ((Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 Q)).coeff k).natDegree ≤ _
  rw [Polynomial.coeff_map]
  apply (unique_degree_le_totalDegree R _).trans
  by_cases h : (MvPolynomial.finSuccEquiv R 1 Q).coeff k = 0
  · simp [h]
  · have hb := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q k h
    omega

theorem nestedY_degree_le (Q : MV R) : (nestedY R Q).natDegree ≤ Q.totalDegree := by
  have h := nestedX_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q)
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem nestedY_coefficient_degree_le (Q : MV R) (k : ℕ) :
    ((nestedY R Q).coeff k).natDegree ≤ Q.totalDegree := by
  have h := nestedX_coefficient_degree_le R (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1) Q) k
  simpa only [MvPolynomial.totalDegree_renameEquiv, nestedY, AlgEquiv.trans_apply] using h

theorem partial_totalDegree_le (Q : MV R) (i : Fin 2) :
    (MvPolynomial.pderiv i Q).totalDegree ≤ Q.totalDegree-1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hQ := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := MvPolynomial.le_totalDegree hQ
  rw [Finsupp.sum_add_index] at hd
  · simp only [Finsupp.sum_single_index] at hd
    omega
  · simp
  · intros
    rfl

end ErdosCriticalGeometry

end

end Erdos970

end OAI
