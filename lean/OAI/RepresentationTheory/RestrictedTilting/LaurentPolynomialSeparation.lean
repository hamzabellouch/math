import Mathlib

namespace OAI

namespace FiberFunctorProof
open scoped LaurentPolynomial
section
variable {k L : Type*} [Field k] [Infinite k] [Field L] [Algebra k L]

lemma polynomial_eq_of_base_evals (P Q : Polynomial L)
    (h : ∀ t : k, P.eval (algebraMap k L t) = Q.eval (algebraMap k L t)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (FaithfulSMul.algebraMap_injective k L)).mono
  rintro _ ⟨t,rfl⟩
  exact h t

lemma laurent_eq_zero_of_base_evals (P : LaurentPolynomial L)
    (h : ∀ a : kˣ,
      LaurentPolynomial.eval₂ (RingHom.id L) (Units.map (algebraMap k L) a) P = 0) : P = 0 := by
  obtain ⟨n,p,hp⟩ := P.exists_T_pow
  have hp0 : p = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (((Set.finite_singleton (0:k)).infinite_compl).image
      (FaithfulSMul.algebraMap_injective k L).injOn).mono
    rintro b ⟨a,ha,rfl⟩
    let x : kˣ := Units.mk0 a ha
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id L)
      (Units.map (algebraMap k L) x)) hp
    simp only [LaurentPolynomial.eval₂_toLaurent, map_mul, h x, zero_mul,
      Polynomial.eval₂_id] at he
    change p.eval (algebraMap k L a) = Polynomial.eval (algebraMap k L a) 0
    have hx : ((Units.map (algebraMap k L) x : Lˣ) : L) = algebraMap k L a := rfl
    rw [hx] at he
    simpa only [Polynomial.eval_zero] using he
  rw [hp0, map_zero] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_right (IsUnit.ne_zero (LaurentPolynomial.isUnit_T n))

lemma laurent_eq_of_base_evals (P Q : LaurentPolynomial L)
    (h : ∀ a : kˣ,
      LaurentPolynomial.eval₂ (RingHom.id L) (Units.map (algebraMap k L) a) P =
        LaurentPolynomial.eval₂ (RingHom.id L) (Units.map (algebraMap k L) a) Q) : P = Q := by
  apply sub_eq_zero.mp
  apply laurent_eq_zero_of_base_evals (k := k)
  intro a
  rw [map_sub, h a, sub_self]
lemma laurent_eq_of_evals (P Q : LaurentPolynomial k)
    (h : ∀ a : kˣ, LaurentPolynomial.eval₂ (RingHom.id k) a P =
      LaurentPolynomial.eval₂ (RingHom.id k) a Q) : P = Q := by
  have hz (a : kˣ) : LaurentPolynomial.eval₂ (RingHom.id k) a (P-Q) = 0 := by
    rw [map_sub, h a, sub_self]
  obtain ⟨n,p,hp⟩ := (P-Q).exists_T_pow
  have hp0 : p = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply ((Set.finite_singleton (0:k)).infinite_compl).mono
    intro a ha
    let x : kˣ := Units.mk0 a ha
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id k) x) hp
    simp only [LaurentPolynomial.eval₂_toLaurent, map_mul, hz x, zero_mul,
      Polynomial.eval₂_id] at he
    have hx : (x : k) = a := rfl
    rw [hx] at he
    change p.eval a = Polynomial.eval a 0
    simpa only [Polynomial.eval_zero] using he
  rw [hp0, map_zero] at hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp.symm).resolve_right
    (IsUnit.ne_zero (LaurentPolynomial.isUnit_T n)))

end
end FiberFunctorProof

end OAI
