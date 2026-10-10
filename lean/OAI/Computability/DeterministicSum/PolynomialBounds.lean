import Mathlib
import OAI.Computability.DeterministicSum.Interpolation

namespace OAI

/-! Individual-degree bounds and Newton polynomial conversion. -/

namespace DeterministicThreeSum.Newton
open Finset
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] {q d : ℕ}

noncomputable def univariate (node : Fin q → R) (j : Fin q) : Polynomial R :=
  ∏ a ∈ Iio j, (Polynomial.X-Polynomial.C (node a))

lemma univariate_degree (node : Fin q → R) (j : Fin q) :
    (univariate node j).natDegree ≤ j.val := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    have hz : univariate node j = 0 := Subsingleton.elim _ _
    simp [hz]
  have := hR
  apply (Polynomial.natDegree_prod_le _ _).trans
  simp

noncomputable def conversion (node : Fin q → R) (j v : Fin q) : R :=
  (univariate node j).coeff v.val

lemma conversion_zero (node : Fin q → R) (j v : Fin q) (hjv : j < v) :
    conversion node j v = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((univariate_degree node j).trans_lt hjv)

lemma univariate_factor (node : Fin q → R) (j : Fin q) (k : Fin d) :
    (∏ a ∈ Iio j, (MvPolynomial.X k-MvPolynomial.C (node a))) =
      ∑ v : Fin q, MvPolynomial.C (conversion node j v)*MvPolynomial.X k^v.val := by
  classical
  have hpoly := Polynomial.as_sum_range' (univariate node j) q
    ((univariate_degree node j).trans_lt j.isLt)
  have hm := congrArg (Polynomial.toMvPolynomial (R:=R) k) hpoly
  simpa only [univariate,map_prod,map_sub,Polynomial.toMvPolynomial_X,
    Polynomial.toMvPolynomial_C,map_sum,← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
    ← Fin.sum_univ_eq_sum_range,conversion] using hm

lemma basis_expansion (node : Fin q → R) (j : Fin d → Fin q) :
    basisPolynomial node j = ∑ v : Fin d → Fin q,
      MvPolynomial.C (∏ i, conversion node (j i) (v i)) *
        ∏ i : Fin d, MvPolynomial.X i^(v i).val := by
  classical
  unfold basisPolynomial
  simp_rw [univariate_factor]
  rw [Fintype.prod_sum (fun i : Fin d => fun v : Fin q =>
    MvPolynomial.C (conversion node (j i) v)*MvPolynomial.X i^v.val)]
  apply sum_congr rfl
  intro v hv
  rw [prod_mul_distrib,← map_prod]

noncomputable def exponentVector (v : Fin d → Fin q) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).val)
@[simp] lemma exponentVector_apply (v : Fin d → Fin q) (i : Fin d) :
    exponentVector v i = (v i).val := by simp [exponentVector]

lemma indicator_exponentVector (v : Fin d → Fin q) :
    Finsupp.indicator univ (fun i _ => (v i).val) = exponentVector v := by
  ext i
  simp

lemma exponentVector_injective : Function.Injective (exponentVector (d:=d) (q:=q)) := by
  intro v w h
  funext i
  apply Fin.ext
  simpa using congrArg (fun z : Fin d →₀ ℕ => z i) h

lemma coefficient_basis (node : Fin q → R) (j v : Fin d → Fin q) :
    (basisPolynomial node j).coeff (exponentVector v) =
      ∏ i, conversion node (j i) (v i) := by
  classical
  rw [basis_expansion,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_prod_X_pow,
    indicator_exponentVector,exponentVector_injective.eq_iff]
  simp

lemma coefficient_truncated (node : Fin q → R) (f : (Fin d → Fin q) → R)
    (D : ℕ) (v : Fin d → Fin q) :
    (truncatedPolynomial node f D).coeff (exponentVector v) =
      ∑ j : Fin d → Fin q, (if degree j ≤ D then coefficients node f j else 0)*
        ∏ i, conversion node (j i) (v i) := by
  classical
  simp only [truncatedPolynomial,MvPolynomial.coeff_sum,sum_filter]
  apply sum_congr rfl
  intro j hj
  split_ifs <;> simp_all [coefficient_basis]

lemma basis_individual_degree (node : Fin q → R) (j : Fin d → Fin q) (k : Fin d) :
    (basisPolynomial node j).degreeOf k ≤ (j k).val := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    have hz : basisPolynomial node j = 0 := Subsingleton.elim _ _
    simp [hz]
  have := hR
  unfold basisPolynomial
  apply (MvPolynomial.degreeOf_prod_le k _ _).trans
  calc
    (∑ i : Fin d, (∏ a ∈ Iio (j i), (MvPolynomial.X i-MvPolynomial.C (node a))).degreeOf k) ≤
      ∑ i : Fin d, if i=k then (j i).val else 0 := by
      apply sum_le_sum
      intro i hi
      apply (MvPolynomial.degreeOf_prod_le k _ _).trans
      calc
        _ ≤ ∑ _a ∈ Iio (j i), if k=i then 1 else 0 := sum_le_sum (by
          intro a ha
          exact (MvPolynomial.degreeOf_sub_le k _ _).trans (by simp [MvPolynomial.degreeOf_X]))
        _ = _ := by by_cases hik : i=k <;> simp [hik,Ne.symm]
    _ = _ := by simp

lemma truncated_individual_degree (node : Fin q → R) (f : (Fin d → Fin q) → R)
    (D : ℕ) (k : Fin d) (hq : 0 < q) :
    (truncatedPolynomial node f D).degreeOf k < q := by
  classical
  apply (MvPolynomial.degreeOf_sum_le k _ _).trans_lt
  apply Finset.sup_lt_iff hq |>.mpr
  intro j hj
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans_lt
    ((basis_individual_degree node j k).trans_lt (j k).isLt)
end
end DeterministicThreeSum.Newton

end OAI
