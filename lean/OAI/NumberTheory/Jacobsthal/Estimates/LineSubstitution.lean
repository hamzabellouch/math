import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialValueBound

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

noncomputable def lineSub {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R) :
    MvPolynomial (Fin 2) ℤ →+* Polynomial R :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp φ)
    ![Polynomial.X,Polynomial.C a-Polynomial.C s*Polynomial.X]

theorem lineSub_monomial {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (i : MonomialIndex D) (c : ℤ) :
    lineSub φ a s (MvPolynomial.monomial (exponent i) c) =
      Polynomial.C (φ c)*(Polynomial.X^i.2.val *
        (Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val)) := by
  change MvPolynomial.eval₂ (Polynomial.C.comp φ)
    ![Polynomial.X,Polynomial.C a-Polynomial.C s*Polynomial.X]
    (MvPolynomial.monomial (exponent i) c) = _
  rw [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [exponent,Fin.prod_univ_two]

theorem affine_natDegree_le {R : Type*} [CommRing R] (a s : R) :
    (Polynomial.C a-Polynomial.C s*Polynomial.X).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · have h := Polynomial.natDegree_mul_le (p := Polynomial.C s) (q := Polynomial.X)
    simp only [Polynomial.natDegree_C,zero_add] at h
    exact h.trans Polynomial.natDegree_X_le

theorem lineSub_monomial_degree {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (i : MonomialIndex D) (c : ℤ) :
    (lineSub φ a s (MvPolynomial.monomial (exponent i) c)).natDegree ≤ D := by
  have hx : (Polynomial.X^i.2.val : Polynomial R).natDegree ≤ i.2.val := by
    simpa using Polynomial.natDegree_pow_le_of_le i.2.val (Polynomial.natDegree_X_le (R := R))
  have hl : ((Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val)).natDegree ≤ i.1.val-i.2.val := by
    simpa using Polynomial.natDegree_pow_le_of_le (i.1.val-i.2.val) (affine_natDegree_le a s)
  rw [lineSub_monomial]
  have hprod := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial R)^i.2.val)
    (q := (Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val))
  have hC := Polynomial.natDegree_mul_le (p := Polynomial.C (φ c))
    (q := Polynomial.X^i.2.val*(Polynomial.C a-Polynomial.C s*Polynomial.X)^(i.1.val-i.2.val))
  simp only [Polynomial.natDegree_C,zero_add] at hC
  have hk := i.1.isLt
  have hj := i.2.isLt
  exact (hC.trans (hprod.trans (Nat.add_le_add hx hl))).trans (by omega)

theorem lineSub_encode_degree {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (v : MonomialIndex D → ℤ) : (lineSub φ a s (encode v)).natDegree ≤ D := by
  rw [encode,map_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => lineSub_monomial_degree φ a s i (v i))

theorem lineSub_encode_eq_zero {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s : R)
    {D : ℕ} (v : MonomialIndex D → ℤ)
    (h : ∀ k : Fin (D+1), (lineSub φ a s (encode v)).coeff k = 0) :
    lineSub φ a s (encode v) = 0 := by
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k ≤ D
  · exact h ⟨k,by omega⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((lineSub_encode_degree φ a s v).trans_lt (by omega))

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
