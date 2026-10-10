import Mathlib

namespace OAI

/-!
# Removing the top homogeneous component

The homogeneous decomposition expresses the remainder after subtracting a polynomial's
top component as a sum of strictly lower components. If the original total degree is
positive, the finite-sum degree bound makes this a strict degree reduction.
-/

namespace RieszRectifiability

noncomputable section

theorem polynomial_sub_top_eq_lower_sum {σ : Type*} (P : MvPolynomial σ ℂ) :
    P - MvPolynomial.homogeneousComponent P.totalDegree P =
      ∑ n ∈ Finset.range P.totalDegree, MvPolynomial.homogeneousComponent n P := by
  have h := MvPolynomial.sum_homogeneousComponent P
  rw [Finset.sum_range_succ] at h
  exact sub_eq_iff_eq_add.mpr h.symm

theorem polynomial_sub_top_degree_lt {σ : Type*} (P : MvPolynomial σ ℂ)
    (hpos : 0 < P.totalDegree) :
    (P - MvPolynomial.homogeneousComponent P.totalDegree P).totalDegree < P.totalDegree := by
  classical
  rw [polynomial_sub_top_eq_lower_sum]
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _)
  apply (Finset.sup_lt_iff hpos).2
  intro n hn
  exact (MvPolynomial.homogeneousComponent_isHomogeneous n P).totalDegree_le.trans_lt
    (Finset.mem_range.mp hn)

end

end RieszRectifiability

end OAI
