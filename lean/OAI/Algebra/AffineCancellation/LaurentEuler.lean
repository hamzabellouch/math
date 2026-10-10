import OAI.Algebra.AffineCancellation.LaurentDerivation

namespace OAI

noncomputable section

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def linear : LaurentPolynomial R →ₗ[k] LaurentPolynomial R :=
  (Finsupp.lsum k (fun n : ℤ => n • (AddMonoidAlgebra.lsingle n : R →ₗ[k] LaurentPolynomial R))) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
lemma linear_single (n : ℤ) (r : R) : linear (k := k) (C r*T n)=n • (C r*T n) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.lsum k _ (Finsupp.single n r)=_
  rw [Finsupp.lsum_single]
  rfl
lemma linear_mul (r s : LaurentPolynomial R) :
    linear (k := k) (r*s)=r*linear (k := k) s+s*linear (k := k) r := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [add_mul,map_add,hr,hs]; ring
  | C_mul_T n a =>
    induction s using LaurentPolynomial.induction_on' with
    | add r s hr hs => simp only [mul_add,map_add,hr,hs]; ring
    | C_mul_T m b =>
      have he : C a*T n*(C b*T m)=C (a*b)*T (n+m) := by rw [map_mul,T_add]; ring
      rw [he,linear_single,linear_single,linear_single,← he,add_zsmul]
      simp only [mul_smul_comm]
      rw [mul_comm (C b*T m),add_comm]
def derivation : Derivation k (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' linear (by intro r s; exact linear_mul r s)
@[simp] lemma monomial (n : ℤ) (r : R) : derivation (k := k) (C r*T n)=n • (C r*T n) := linear_single n r
@[simp] lemma coefficient (r : R) : derivation (k := k) (C r)=0 := by simpa using monomial (k := k) 0 r
@[simp] lemma T_apply (n : ℤ) : derivation (k := k) (T n : LaurentPolynomial R)=n • T n := by simpa using monomial (k := k) n (1 : R)
end ComplexCancellation.LaurentEuler

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
lemma commute_extension (D : Derivation k R R) (r : LaurentPolynomial R) :
    derivation (k := k) (LaurentDerivation.extension D r)=LaurentDerivation.extension D (derivation (k := k) r) := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [map_add,hr,hs]
  | C_mul_T n a => rw [LaurentDerivation.extension_monomial (k := k),monomial (k := k),monomial (k := k),map_zsmul,LaurentDerivation.extension_monomial (k := k)]
lemma commute_replica (D : Derivation k R R) (c : R) (r : LaurentPolynomial R) :
    derivation (k := k) (C c*LaurentDerivation.extension D r)=C c*LaurentDerivation.extension D (derivation (k := k) r) := by
  rw [Derivation.leibniz,coefficient,smul_zero,add_zero,smul_eq_mul,commute_extension]
end ComplexCancellation.LaurentEuler

end

end OAI
